{-# options_ghc -Wno-unused-imports #-}

module Elaboration (elab, Top(..), TopDef(..), retryProblem, retryAllProblems, Check(..)) where

import Common hiding (Set)
import Core.Syntax (Tm, Ty, Tm0, LocalsArg, Locals(..))
import Core.Value
import Core.Info
import Evaluation
import Elaboration.State
import Errors
import Config
import Pretty

import Presyntax   qualified as P
import Core.Syntax qualified as S
import Unification qualified as U

--------------------------------------------------------------------------------

{- TODO:
- Define a bunch of "semantic" functions for (Tm,Val) pairs.
- Use this "Epigram" glued type in Check and Infer.
- Proper coercion to Set in type position!
- Remember user-given icitness for default printing.
- Toggle explicit/implicit printing.

Restructure things around the (Tm,Val) pairs!
-}

type Elab a = LvlArg => EnvArg => LocalsArg => SrcArg => LazySpanArg => a

{-# inline forceElab #-}
forceElab :: Elab a -> Elab a
forceElab act = seq ?lvl (seq ?env (seq ?locals (seq ?src (seq ?span act))))

-- | Add a local definitiíon.
{-# inline define #-}
define :: Name -> Ty -> VTy -> Tm -> Val -> Elab (Val -> IO a) -> Elab (IO a)
define x a va t vt act = do
  let val     = LocalDef ?lvl va vt
  let ?lvl    = ?lvl + 1
      ?env    = EDef ?env val
      ?locals = LDef ?locals x t a
  forceElab $ localDefineIS x va (act val)

-- | Add a bound variable.
{-# inline bind #-}
bind :: Name -> Ty -> VTy -> Elab (Val -> IO a) -> Elab (IO a)
bind x a va act = do
  let val     = LocalVar ?lvl va
  let ?lvl    = ?lvl + 1
      ?env    = EBind ?env val
      ?locals = LBind ?locals x a
  forceElab $ localDefineIS x va (act val)

-- | Insert a new binder (don't update the identifier scope since
--   the new binder doesn't exist in presyntax).
{-# inline insertBind #-}
insertBind :: Name -> Ty -> VTy -> Elab (Val -> IO a) -> Elab (IO a)
insertBind x a va act = do
  let val     = LocalVar ?lvl va
  let ?lvl    = ?lvl + 1
      ?env    = EBind ?env val
      ?locals = LBind ?locals x a
  forceElab $ act val

{-# inline forcePTm #-}
forcePTm :: P.Tm -> (LazySpanArg => P.Tm -> a) -> a
forcePTm t act = go t where
  go (P.Parens _ t _) = go t
  go t                = let ?span = LazySpan (spanOf t) in act t

bindToName :: P.Bind -> Name
bindToName = \case
  P.BOp _ op _   -> NOp op
  P.BName x      -> NSrcName x
  P.BUnused _    -> N_
  P.BNonExistent -> N_

elabError :: Dbg => LvlArg => LocalsArg => SrcArg => LazySpanArg => Error -> IO a
elabError err = throwIO $ ErrorInCxt ?src ?locals ?lvl ?span err

noStage0 :: Dbg => LvlArg => LocalsArg => SrcArg => LazySpanArg => IO a
noStage0 = elabError "Stage 0 is not yet supported"

noOps :: Dbg => LvlArg => LocalsArg => SrcArg => LazySpanArg => IO a
noOps = elabError "Operators are not yet supported"

noInductive :: Dbg => LvlArg => LocalsArg => SrcArg => LazySpanArg => IO a
noInductive = elabError "Inductive types are not yet supported"

unify :: Elab (GVal -> GVal -> IO ())
unify l r = do
  let ?unifyState = U.USPrecise conversionSpeculation
  debug ["UNIFY", pretty (readbNoUnfold (g1 l)), pretty (readbNoUnfold (g1 r))]
  uf
  -- U.unify l r _
  -- U.unify l r `catch`
  --   \(e :: U.UnifyEx) -> elabError $ UnifyError (g1 l) (g1 r) e

--------------------------------------------------------------------------------

data Check = Check Tm ~Val
data Infer = Infer Tm ~VTy ~Val

checkAnnotation :: Elab (Maybe P.Tm -> GTy -> IO Check)
checkAnnotation t a = case t of
  Nothing -> elabError MissingAnnotation
  Just t  -> check t a

postponeCheck :: Elab (IO Check -> VTy -> MetaVar -> IO Check)
postponeCheck action a blocker = do

  -- create placeholder meta
  m <- newMeta (readbNoUnfold a)

  -- create problem
  id <- newProblem $ PCheck action m

  -- register blocker
  newlyBlocked blocker id

  -- return placeholder
  pure $ Check (S.Meta m S.MSId) (Flex (FHMeta (MetaHead m ?env)) SId)


checkLamMultiBind :: Elab (List P.Bind -> Icit -> List P.MultiBind -> P.Tm -> GTy -> IO Check)
checkLamMultiBind topxs i binds t (G b fb) = do
  case topxs of
    Nil -> do
      checkLam binds t (G b fb)

    -- GHCI bug: -O1 compilation works with "case whnf fb of", but GHCI only works with "whnfIO fb"!
    Cons (bindToName -> x) xs -> whnfIO fb >>= \case
      -- go under lambda
      Pi b | b^.icit == i -> do
        let va = b^.ty
            a  = readbNoUnfold va
        Check t vt <- bind x a va \v -> do
          checkLamMultiBind xs i binds t (gjoin (b ∙ v))
        pure $ Check (S.Lam (BindI x i a t)) (Lam $ ClI x i va \v -> def v \_ -> eval t)

      -- insert implicit lambda
      Pi b | b^.icit == Impl -> do
        let x  = b^.name
            va = b^.ty
            a  = readbNoUnfold va
        Check t vt <- insertBind x a va \v -> do
          checkLamMultiBind topxs i binds t (gjoin (b ∙ v))
        pure $ Check (S.Lam (BindI x Impl a t)) (Lam $ ClI x Impl va \v -> def v \_ -> eval t)

      -- postpone checking
      fb@(Flex (FHMeta (MetaHead blocker _)) _) -> do
        debug ["POSTPONE CHECKLAM"]
        postponeCheck (checkLamMultiBind topxs i binds t (G b fb)) b blocker

      _ -> elabError $ NonFunctionForLambda b

checkLam :: Elab (List P.MultiBind -> P.Tm -> GTy -> IO Check)
checkLam binds t b = case binds of
  Nil -> do
    check t b
  Cons (P.MultiBind xs i Nothing) binds -> do
    checkLamMultiBind xs i binds t b
  Cons (P.MultiBind xs i Just{}) binds ->
    elabError "Annotated lambdas are not yet supported"

retryProblem :: Int -> IO ()
retryProblem i = lookupProblem i >>= \case
  PCheck action placeholder -> do
    debug ["RETRY CHECK", show i]
    problemSolved i
    Check t vt <- action
    case lookupMeta placeholder of
      MESolved e   -> unify (gjoin vt) (gjoin (eval (e^.solution)))
      MEUnsolved e -> newSolution placeholder ?locals (e^.ty) t
      MESolved0{}  -> impossible
  PSolved -> pure ()

retryAllProblems :: IO ()
retryAllProblems = uf

check :: Elab (P.Tm -> GTy -> IO Check)
check t gtopA@(G topA ftopA) = forcePTm t \t -> do
  debug ["CHECK", show t, prettyReadb topA]
  case t of
    P.Parens{} -> impossible

    P.Hole _ -> do
      elabError "holes are not yet supported"

    P.Inferred _ -> do
      m <- U.freshMeta (readbNoUnfold topA)
      pure $ Check m (eval m)

    P.Lam _ binds t -> checkLam binds t gtopA

    topt -> whnfIO ftopA >>= \case

      -- insert implicit lambda
      Pi b | b^.icit == Impl -> do
        let x  = b^.name
            va = b^.ty
            a  = readbNoUnfold va
        Check t vt <- insertBind x a va \v -> check topt (gjoin (b ∙ va))
        pure $ Check (S.Lam (BindI x Impl a t)) (Lam $ ClI x Impl va \v -> def v \_ -> eval t)

      -- postpone checking
      ftopA@(Flex (FHMeta (MetaHead blocker _)) _) -> do
        postponeCheck (check topt (G topA ftopA)) topA blocker

      ftopA -> case topt of

        P.Let _ S1 (bindToName -> x) a t u -> do
          Check a va <- checkAnnotation a gSet
          Check t vt <- check t (gjoin va)
          Check u _  <- define x a va t vt \_ -> do
            check u (G topA ftopA)
          -- We have non-trivial strengthening for the value under the Let,
          -- because of the local unfolding preservation!
          -- We get rid of LocaDef-s by re-evaluating the body.
          pure $ Check (S.Let t (Bind x a u)) (def vt \_ -> eval u)

        topt -> do
          t@(Infer _ a _) <- infer topt
          -- debug ["INFERRED", pretty (readbNoUnfold a)]
          coeChk t (G topA ftopA)

insertApp :: Elab (Tm -> ClosureI -> Val -> IO Infer)
insertApp t a ~vt = do
  m <- U.freshMeta (readbNoUnfold (a^.ty))
  let ~vm = eval m
  pure $! Infer (t ∘ m) (a ∙ vm) (vt ∘ vm)

-- coercion in check
-- we already know that the target type cannot be an implicit function
-- so we only need to insert args until the source type is not an implicit fun type anymore,
-- and then unify types
coeChk :: Elab (Infer -> GTy -> IO Check)
coeChk (Infer t a vt) a' = whnfIO a >>= \case
  Pi b | b^.icit == Impl -> do
    inf <- insertApp t b vt
    coeChk inf a'
  fa -> do
    unify (G a fa) a'
    pure $ Check t vt

-- coerce to explicit function type
coeToPiExpl :: Elab (Infer -> IO (Tm, VTy, WithLvl (Val -> Val), Val))
coeToPiExpl (Infer t a vt) = whnfIO a >>= \case
  Pi a  -> case a^.icit of
    Impl -> insertApp t a vt >>= coeToPiExpl
    Expl -> pure (t, a^.ty, WithLvl (boxLvlArg (a^.body)), vt)
  _ ->
    elabError "expected a function type"

inferSp :: Elab (P.Spine b -> Infer -> IO Infer)
inferSp sp hd@(Infer t a vt) = do
  -- debug ["INFERSP", show sp, show (readbNoUnfold a)]
  case sp of
    P.SNil          -> pure hd
    P.STm u Expl sp -> do
      (t, a, WithLvl b, vt)  <- coeToPiExpl hd
      Check u vu <- check u (gjoin a)
      inferSp sp (Infer (t ∙ u) (b vu) (vt ∙ vu))
    P.STm u Impl sp -> whnfIO a >>= \case -- TODO: coercion to implicit Pi
      Pi a | a^.icit == Impl -> do    --   (when we have more coercions)
        Check u vu <- check u (gjoin (a^.ty))
        inferSp sp (Infer (t ∘ u) (a ∙ vu) (vt ∙ vu))
      _ -> elabError "expected an implicit function type"

    P.SOp{}; P.SProjOp{} -> noOps

-- TODO: let-bind the multi-binder type to avoid term duplication.
--       In that case, we can get probably drop the Wk from syntax.
checkPiMultiBind :: Elab (List P.Bind -> Icit -> Check -> List P.MultiBind -> P.Tm -> IO Check)
checkPiMultiBind xs i (Check a va) binds b = case xs of
  Nil ->
    checkPi binds b
  Cons (bindToName -> x) xs -> do
    Check b vb <- bind x a va \_ -> checkPiMultiBind xs i (Check (S.Wk a) va) binds b
    pure $ Check (S.Pi (BindI x i a b)) (Pi $ ClI x i va \v -> def v \_ -> eval b)

checkPi :: Elab (List P.MultiBind -> P.Tm -> IO Check)
checkPi binds b = case binds of
  Nil -> do
    check b gSet
  Cons (P.MultiBind xs i a) binds -> do
    a <- checkAnnotation a gSet
    checkPiMultiBind xs i a binds b

coeToRecord :: Elab (Infer -> IO (Tm, RecInfo, Spine, Val))
coeToRecord (Infer t a vt) = whnfIO a >>= \case
  Rec i args             -> pure (t, i, args, vt)
  Pi a | a^.icit == Impl -> insertApp t a vt >>= coeToRecord
  _                      -> elabError "expected a record type for projected expression"

infer :: Elab (P.Tm -> IO Infer)
infer t = forcePTm t \case

  P.Let _ S0 _ _ _ _; P.Decl0{}; P.LetRec{}; P.Ty{}; P.Lift{}; P.Quote{}; P.Splice{};
    P.ValTy{}; P.CompTy{}; P.ElVal{}; P.ElComp{} -> noStage0

  P.Unparsed{} -> noOps
  P.Lam{} -> elabError "Can't infer type for lambda"

  P.Parens{} -> impossible

  P.Let _ S1 (bindToName -> x) a t u -> do
    Check a va    <- checkAnnotation a gSet
    Check t vt    <- check t (gjoin va)
    Infer u _ uty <- define x a va t vt \_ -> infer u

    -- strengthenings!
    uty <- pure (readbNoUnfold uty)
    pure $ Infer (S.Let t (Bind x a u)) (def vt \_ -> eval uty) (def vt \_ -> eval u)

  P.Spine t ts -> do
    t <- infer t
    inferSp ts t

  P.Set _ _ -> pure $ Infer S.Set Set Set

  P.Pi _ binds b -> do
    Check t vt <- checkPi binds b
    pure $ Infer t Set vt

  P.Hole _ ->
    elabError "Holes not yet supported"

  P.Inferred _ -> do
    a <- U.freshMeta S.Set
    let va = eval a
    t <- U.freshMeta a
    let vt = eval t
    pure $ Infer t va vt

  P.Ident x -> do
    -- debug ["INFER IDENT", show x]
    lookupIS (NSrcName x) >>= \case
      Nothing -> elabError $ Generic $ "Name not in scope: " ++ show x
      Just e  -> case e of

        ISLocal i -> do
          let var = S.LocalVar (lvlToIx ?lvl (i^.lvl))
          pure $! Infer var (i^.ty) (eval var)

        ISShadowedLocal i _ -> do
          let var = S.LocalVar (lvlToIx ?lvl (i^.lvl))
          pure $! Infer var (i^.ty) (eval var)

        ISTopDef i     -> pure $! Infer (S.TopDef i) (i^.vTy) (i^.value)
        ISTopRecTCon i -> pure $! Infer (S.Rec i) (i^.tConTy) (i^.tConValue)
        ISTopRecDCon i -> pure $! Infer (S.Rec i) (i^.dConTy) (i^.dConValue)
        ISTopTCon{}; ISTopDCon{} -> noInductive
        ISTopDef0{}; ISTopRec0{}; ISTopTCon0{} -> noStage0

  P.LocalLvl x l _ -> lookupIS (NSrcName x) >>= \case
    Nothing -> elabError $ Generic $ "Name not in scope: " ++ show x
    Just e -> elabError $ "De Bruijn local variables not yet supported"
    -- Just e  -> case e of
    --   ISShadowedLocal i e -> do

    --     let go :: ISEntry -> IO (Lvl, Maybe Infer)
    --         go (ISShadowedLocal i e) = do
    --           (l', res) <- go e
    --           if l == l' then do
    --             let var = S.LocalVar (lvlToIx ?lvl (i^.lvl))
    --             let res = Infer var (i^.ty) (eval var)
    --             pure $! (l' + 1 // Just res)
    --           else
    --             pure $! (l' + 1 // res)
    --         go _ =
    --           pure (0, Nothing)

    --     (snd ! go e) >>= \case
    --       Nothing  -> elabError $ Generic $
    --                      "Local name " ++ show x ++
    --                      " not in scope with level " ++ show l
    --       Just res -> pure res

    --   ISLocal i ->

    --   _     -> elabError $ Generic $ "Local name not in scope: " ++ show x

  P.Dot t p -> do
    t <- infer t
    (t, i, args, vt) <- coeToRecord t
    case p of
      P.POp{} -> noOps

      P.PName x -> do
        let go :: FieldInfo -> Ix -> IO Infer
            go FINil _ = elabError $ Generic $ "No such record field: " ++ show x
            go (FISnoc fs x' i a) ix =
              if NSrcName x == x' then do
                let p   = Proj ix x'
                let env = recFieldEnv fs p args vt
                let ~ty = evalE env a
                pure $ Infer (S.Project t p) ty (proj vt p)
              else
                go fs (ix - 1)
        go (i^.fields) 0

      P.PLvl _ lvl _ -> do
        let topIx = lvlToIx (i^.numFields) lvl
        let go :: FieldInfo -> Ix -> IO Infer
            go FINil _ = elabError $ Generic $ "No record field with index " ++ show lvl
            go (FISnoc fs x _ a) 0  = do
              let p   = Proj topIx x
              let env = recFieldEnv fs p args vt
              let ~ty = evalE env a
              pure $ Infer (S.Project t p) ty (proj vt p)
            go (FISnoc fs _ _ a) ix = go fs (ix - 1)
        go (i^.fields) topIx

  P.Rec _ fs _ -> elabError "anonymous record construction not yet supported"


-- Top
--------------------------------------------------------------------------------

newtype TopDef = TopDef DefInfo

instance Show TopDef where
  show (TopDef inf) = show (inf^.name, inf^.ty, inf^.body)

data Top
  = TNil
  | TDef1 {-# nounpack #-} TopDef MetaVar Top
  deriving Show

{-# inline forcePTop #-}
forcePTop :: P.Top -> (LazySpanArg => P.Top -> a) -> a
forcePTop t act = let ?span = LazySpan (spanOf t) in act t

checkTopShadowing :: Elab (Name -> IO ())
checkTopShadowing x = lookupIS x >>= \case
  Nothing -> pure ()
  Just{}  -> elabError $ TopLevelShadowing x

-- | Add a top-level definition.
{-# inline defineTop #-}
defineTop :: Name -> Ty -> VTy -> Tm -> Val -> Elab (DefInfo -> IO a) -> Elab (IO a)
defineTop x a va t vt act = do
  checkTopShadowing x
  uid <- newUid
  let info = DI uid x t (Unfold (UHTopDef info) SId vt) a va -- note the knot!
  topDefineIS info
  act info

elab :: Elab (P.Top -> IO Top)
elab top = reset >> go top where

  go :: Elab (P.Top -> IO Top)
  go t = forcePTop t \case
    P.TNil{} -> pure TNil
    P.TInductive1{} -> noInductive
    P.TDef _ S0 _ _ _; P.TInductive0{};P.TDecl{} -> noStage0

    P.TDef (bindToName -> x) S1 a t top -> do
      Check a va <- checkAnnotation a gSet
      Check t vt <- check t (gjoin va)
      frz <- freezeMetas
      defineTop x a va t vt \inf -> TDef1 (TopDef inf) frz ! go top

    P.TRecord _ (bindToName -> x) c d e f -> do
      uf
