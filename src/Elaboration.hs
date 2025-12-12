{-# options_ghc -Wno-unused-imports #-}

module Elaboration where

import Common hiding (Set)
import Core.Syntax (Tm, Ty, Tm0, LocalsArg, Locals(..))
import Core.Value
import Core.Info
import Evaluation
import Elaboration.State
import Errors
import Config

import Presyntax   qualified as P
import Core.Syntax qualified as S
import Unification qualified as U

--------------------------------------------------------------------------------

{- TODO:
Define a bunch of "semantic" functions for (Tm,Val) pairs.
Use this "Epigram" glued type in Check and Infer.

Restructure things around the (Tm,Val) pairs!
-}

type PTmArg = (?ptm :: P.Tm)

type Elab a = LvlArg => EnvArg => LocalsArg => SrcArg => PTmArg => a

{-# inline forceElab #-}
forceElab :: Elab a -> Elab a
forceElab act = seq ?lvl (seq ?env (seq ?locals (seq ?src act)))

-- | Add a local definition.
{-# inline define #-}
define :: Name -> Ty -> VTy -> Tm -> Val -> Elab (Val -> IO a) -> Elab (IO a)
define x a va t vt act =
  let val     = LocalDef ?lvl va vt in
  let ?lvl    = ?lvl + 1
      ?env    = EDef ?env val
      ?locals = LDef ?locals x t a in
  forceElab $ localDefineIS x va (act val)

-- | Add a bound variable.
{-# inline bind #-}
bind :: Name -> Ty -> VTy -> Elab (Val -> IO a) -> Elab (IO a)
bind x a va act =
  let val     = LocalVar ?lvl va in
  let ?lvl    = ?lvl + 1
      ?env    = EDef ?env val
      ?locals = LBind ?locals x a in
  forceElab $ localDefineIS x va (act val)

-- | Insert a new binder (don't update the identifier scope since
--   the new binder doesn't exist in presyntax).
{-# inline insertBind #-}
insertBind :: Name -> Ty -> VTy -> Elab (Val -> IO a) -> Elab (IO a)
insertBind x a va act =
  let val     = LocalVar ?lvl va in
  let ?lvl    = ?lvl + 1
      ?env    = EDef ?env val
      ?locals = LBind ?locals x a in
  forceElab $ act val

{-# inline forcePTm #-}
forcePTm :: P.Tm -> (PTmArg => P.Tm -> a) -> a
forcePTm t act = go t where
  go (P.Parens _ t _) = go t
  go t                = let ?ptm = t in act t

bindToName :: P.Bind -> Name
bindToName = \case
  P.BOp op       -> NOp op
  P.BName x      -> NRawName x
  P.BUnused _    -> N_
  P.BNonExistent -> N_

elabError :: LvlArg => LocalsArg => SrcArg => PTmArg => Error -> IO a
elabError err = throwIO $ ErrorInCxt ?src ?locals ?lvl ?ptm err

noStage0 :: LvlArg => LocalsArg => SrcArg => PTmArg => IO a
noStage0 = elabError "Stage 0 is not yet supported"

noOps :: LvlArg => LocalsArg => SrcArg => PTmArg => IO a
noOps = elabError "Operators are not yet supported"

noInductive :: LvlArg => LocalsArg => SrcArg => PTmArg => IO a
noInductive = elabError "Inductive types are not yet supported"

unify :: LvlArg => Val -> Val -> IO ()
unify l r = do
  let ?unifyState = U.USPrecise conversionSpeculation
  U.unify (gjoin l) (gjoin r)

--------------------------------------------------------------------------------

data Check = Check Tm ~Val
data Infer = Infer Tm ~VTy ~Val

checkAnnotation :: Elab (Maybe P.Tm -> VTy -> IO Check)
checkAnnotation t a = case t of
  Nothing -> elabError MissingAnnotation
  Just t  -> check t a

checkLamMultiBind :: Elab (List P.Bind -> Icit -> Check -> List P.MultiBind -> P.Tm -> VTy -> IO Check)
checkLamMultiBind xs i (Check a va) binds t b = case xs of
  Nil -> checkLam binds t b

  Cons (bindToName -> x) xs -> case whnf b of
    -- go under lambda
    Pi b | b^.icit == i -> bind x a va \v -> do
      Check t vt <- checkLamMultiBind xs i (Check (S.Wk a) va) binds t (b ∙ v)
      pure $ Check (S.Lam (BindI x i a t)) (Lam $ ClI x i va \v -> def v \_ -> eval t)

    -- insert implicit lambda
    Pi b | b^.icit == Impl -> do
      let x      = b^.name
          vdomty = b^.ty
          domty  = readbNoUnfold vdomty
      insertBind x domty vdomty \v -> do
        Check t vt <- checkLamMultiBind xs i (Check (S.Wk a) va) binds t (whnf (b ∙ v))
        pure $ Check (S.Lam (BindI x Impl domty t)) (Lam $ ClI x Impl vdomty \v -> def v \_ -> eval t)

    _ -> elabError $ NonFunctionForLambda b

checkLam :: Elab (List P.MultiBind -> P.Tm -> VTy -> IO Check)
checkLam binds t b = case binds of
  Nil -> do
    check t b
  Cons (P.MultiBind xs i a) binds -> do
    a <- checkAnnotation a Set
    checkLamMultiBind xs i a binds t b

check :: Elab (P.Tm -> VTy -> IO Check)
check t topA = forcePTm t \case

  P.Parens{} -> impossible

  P.Let _ S1 (bindToName -> x) a t u -> do
    Check a va <- checkAnnotation a Set
    Check t vt <- check t va
    Check u _  <- define x a va t vt \_ -> check u topA
    -- We have non-trivial strengthening for the value under the Let,
    -- because of the local unfolding preservation!
    -- We get rid of LocaDef-s by re-evaluating the body.
    pure $ Check (S.Let t (Bind x a u)) (def vt \_ -> eval u)

  P.Hole _ -> do
    m <- U.freshMeta (readbNoUnfold topA)
    pure $ Check m (eval m)

  -- TODO: reconsider the whnf-ing of topA here
  --       ensure that holes get non-whnf-ed types!
  topt -> case topt of
    P.Lam _ binds t -> checkLam binds t topA
    topt            -> do t <- infer topt; coeChk t topA

insertApp :: Elab (Tm -> ClosureI -> Val -> IO Infer)
insertApp t a ~vt = do
  m <- U.freshMeta (readbNoUnfold (a^.ty))
  let ~vm = eval m
  pure $! Infer (t ∘ m) (a ∙ vm) (vt ∘ vm)

-- coercion in check
-- we already know that the target type cannot be an implicit function
-- so we only need to insert args until the source type is not an implicit fun type anymore,
-- and then unify types
coeChk :: Elab (Infer -> VTy -> IO Check)
coeChk (Infer t a vt) a' = case whnf a of
  Pi b | b^.icit == Impl -> do
    inf <- insertApp t b vt
    coeChk inf a'
  a -> do
    unify a a'
    pure $ Check t vt

-- coerce to explicit function type
coeToPiExpl :: Elab (Infer -> IO (VTy, Val -> Val))
coeToPiExpl (Infer t a vt) = case whnf a of
  Pi a  -> case a^.icit of
    Impl -> insertApp t a vt >>= coeToPiExpl
    Expl -> pure (a^.ty, a^.body)
  _ ->
    elabError "expected a function type"

inferSp :: Elab (P.Spine b -> Infer -> IO Infer)
inferSp sp hd@(Infer t a vt) = case sp of
  P.SNil          -> pure hd
  P.STm u Expl sp -> do
    (t, a, b, vt)  <- coeToPiExpl hd
    Check u vu <- check u a
    pure $! Infer (t ∙ u) (b vu) (vt ∙ vu)
  P.STm u Impl sp -> case whnf a of
    Pi a | a^.icit == Impl -> do
      Check u vu <- check u (a^.ty)
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
    check b Set
  Cons (P.MultiBind xs i a) binds -> do
    a <- checkAnnotation a Set
    checkPiMultiBind xs i a binds b

coeToRecord :: Elab (Infer -> IO (Tm, Val, RecInfo, Spine))
coeToRecord (Infer t a vt) = case whnf a of
  Rec i args             -> pure (i, args)
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
    Check a va    <- checkAnnotation a Set
    Check t vt    <- check t va
    Infer u _ uty <- define x a va t vt \_ -> infer u

    -- strengthenings!
    uty <- pure (readbNoUnfold uty)
    pure $ Infer (S.Let t (Bind x a u)) (def vt \_ -> eval uty) (def vt \_ -> eval u)

  P.Spine t ts -> inferSp ts =<< infer t

  P.Set _ _ -> pure $ Infer S.Set Set Set

  P.Pi _ binds b -> do
    Check t vt <- checkPi binds b
    pure $ Infer t Set vt

  P.Hole _ -> do
    elabError "hole not yet supported"

  P.Inferred _ -> do
    elabError "can't infer placeholder"

  P.Ident x -> lookupIS (NRawName x) >>= \case
    Nothing -> elabError $ Generic $ "Name not in scope: " ++ show x
    Just e  -> case e of
      ISLocal i _ -> pure $! Infer (S.LocalVar (lvlToIx ?lvl (i^.lvl)))
                                   (i^.ty) (LocalVar (i^.lvl) (i^.ty))
      ISNil       -> impossible
      ISTopDef i  -> pure $! Infer (S.TopDef i) (i^.ty) (i^.value)
      ISTopRec i  -> pure $! Infer (S.Rec i) (i^.ty) (i^.value)
      ISTopTCon{}; ISTopDCon{} -> noInductive
      ISTopDef0{}; ISTopRec0{}; ISTopTCon0{} -> noStage0

  P.LocalLvl x l _ -> lookupIS (NRawName x) >>= \case
    Nothing -> elabError $ Generic $ "Name not in scope: " ++ show x
    Just e  -> case e of
      ISLocal i e -> do

        let go :: ISEntry -> IO (Lvl, Maybe Infer)
            go (ISLocal i e) = do
              (l', res) <- go e
              if l == l' then do
                let res = Infer (S.LocalVar (lvlToIx ?lvl (i^.lvl)))
                                 (i^.ty) (LocalVar (i^.lvl) (i^.ty))
                pure $! (l' + 1 // Just res)
              else
                pure $! (l' + 1 // res)
            go _ =
              pure (0, Nothing)

        (snd ! go e) >>= \case
          Nothing  -> elabError $ Generic $
                         "Local name " ++ show x ++
                         " not in scope with level " ++ show l
          Just res -> pure res

      ISNil -> impossible
      _     -> elabError $ Generic $ "Local name not in scope: " ++ show x

  P.Dot t p -> do
    t <- infer t
    (t, i, args, vt) <- coeToRecord t
    case p of
      P.PName x -> do
        let go :: FieldInfo -> IO Infer
            go FINil = elabError $ Generic $ "No such record field: " ++ show x
            go (FISnoc fs x' i a)
              | NRawName x == x' = pure _
              | otherwise        = go fs
        go (i^.fields)


--------------------------------------------------------------------------------
