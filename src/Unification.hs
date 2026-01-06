
module Unification where

import Data.IntMap (IntMap)
import Data.IntMap qualified as IM
import Data.IntSet qualified as IS
import Data.Ref.F  qualified as RF

import Common
import Core.Info
import Core.Syntax (Ty, Tm, LocalsArg, Tm0)
import Core.Syntax qualified as S
import Core.Value
import Elaboration.State qualified as ES
import {-# source #-} Elaboration

import Evaluation
import Utils.State

import Pretty

----------------------------------------------------------------------------------------------------

freshMeta :: LocalsArg => Ty -> IO Tm
freshMeta a = S.Meta ! ES.newMeta a ∙ pure S.MSId

data UnifyEx = UETodo deriving Show
instance Exception UnifyEx

data InversionEx = InversionEx MetaVar deriving Show
instance Exception InversionEx

unifyError :: Dbg => IO a
unifyError = throwIO UETodo

catchUnify :: IO a -> IO a -> IO a
catchUnify act otherwise = catch @UnifyEx act \_ -> otherwise

-- Partial substitutions
----------------------------------------------------------------------------------------------------

newtype MultiClosure a = MCl (LvlArg => [Val] -> a)
instance Show (MultiClosure a) where show _ = "<closure>"
instance Apply LvlArg (MultiClosure Val) [Val] Val where
  MCl f ∙∘ (e,_) = f e; {-# inline (∙∘) #-}

data PartialRecFields
  = PRFNil
  | PRFSnoc PartialRecFields PartialVal Icit
  deriving Show

instance ElemAt PartialRecFields Ix PartialVal where
  elemAt ts i = case (ts, i) of
    (PRFSnoc _ v _  , 0) -> v
    (PRFSnoc ts _ _, i)  -> elemAt ts (i - 1)
    _                    -> impossible

instance UpdateAt PartialRecFields Ix PartialVal where
  {-# inline updateAt #-}
  updateAt ts ix f = go ts ix where
    go (PRFSnoc ts v i) 0  = PRFSnoc ts (f v) i
    go (PRFSnoc ts v i) ix = PRFSnoc (go ts (ix - 1)) v i
    go _                _  = impossible

data PartialVal
  = PVTop
  | PVBot
  | PVQuote PartialVal0
  | PVTotal (MultiClosure Val)
  | PVLam Name Icit (MultiClosure Val) PartialVal
  | PVRec {-# nounpack #-} RecInfo PartialRecFields
  deriving Show

data PartialVal0
  = PV0Top
  | PV0Bot
  | PV0Total Val0
  deriving Show

data PSubEntry
  = PSEVal  PartialVal
  | PSEVal0 PartialVal0
  deriving Show

data PartialSub = PSub {
    partialSubOccurs       :: Maybe MetaVar    -- ^ Optional meta occurs check
  , partialSubAllowPruning :: Bool             -- ^ Can we prune metas
  , partialSubIsLinear     :: Bool             -- ^ Does the sub contain PVTop
  , partialSubDomEnv       :: Env              -- ^ Identity environment for the domain
  , partialSubDom          :: Lvl              -- ^ Domain (size of the map)
  , partialSubCod          :: Lvl              -- ^ Codomain (next fresh Lvl)
  , partialSubSub          :: IntMap PSubEntry -- ^ Map from codomain vars to partial values.
                                               --   Missing entries are Bot.
  }

makeFields ''PartialSub
deriving instance Show PartialSub

evalInDom :: Eval a b => PSubArg => a -> b
evalInDom a = let ?lvl = ?psub^.dom; ?env = ?psub^.domEnv in eval a

forceInCod :: PSubArg => Val -> Val
forceInCod v = let ?lvl = ?psub^.cod in force v

force0InCod :: PSubArg => Val0 -> Val0
force0InCod v = let ?lvl = ?psub^.cod in force0 v

readbInDom :: PSubArg => ReadBack a b => UnfoldArg => a -> b
readbInDom a = let ?lvl = ?psub^.dom in readb a

inversionError :: Dbg => PartialSub -> IO a
inversionError psub = maybe impossible (throwIO . InversionEx) (psub^.occurs)

type PSubArg = (?psub :: PartialSub)

setPSub :: PartialSub -> (PSubArg => a) -> a
setPSub s act = let ?psub = s in act

class Merge a where
  merge :: a -> a -> State Bool a

instance Merge PartialRecFields where
  merge (PRFNil        ) (PRFNil        ) = pure PRFNil
  merge (PRFSnoc ts t i) (PRFSnoc us u _) = PRFSnoc ! merge ts us ∙ merge t u ∙ pure i
  merge (_             ) (_             ) = impossible

instance Merge PartialVal where
  merge (PVBot        ) (u            ) = pure u
  merge (t            ) (PVBot        ) = pure t
  merge (PVLam x i a t) (PVLam _ _ _ u) = PVLam x i a ! merge t u
  merge (PVRec i ts   ) (PVRec _ us   ) = PVRec i ! merge ts us
  merge (_            ) (_            ) = PVTop <$ put False

instance Merge PartialVal0 where
  merge (PV0Bot) (u     ) = pure u
  merge (t     ) (PV0Bot) = pure t
  merge (_     ) (_     ) = PV0Top <$ put False

instance Merge PSubEntry where
  merge (PSEVal  pv) (PSEVal  pv') = PSEVal  ! merge pv pv'
  merge (PSEVal0 pv) (PSEVal0 pv') = PSEVal0 ! merge pv pv'
  merge (_         ) (_          ) = impossible

lift :: VTy -> PartialSub -> PartialSub
lift ~a (PSub occ pr lin idenv dom cod sub) =
  let var = LocalVar dom a in
  PSub occ pr lin (EDef idenv var) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PSEVal (PVTotal (MCl \_ -> var))) sub

lift0 :: PartialSub -> PartialSub
lift0 (PSub occ pr lin idenv dom cod sub) =
  let var = LocalVar0 dom in
  PSub occ pr lin (EBind0 idenv var) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PSEVal0 (PV0Total var)) sub

updatePSub :: PartialSub -> Lvl -> PartialVal -> PartialSub
updatePSub psub x (PSEVal -> pv) = case IM.lookup (fromIntegral x) (psub^.sub) of
  Nothing    -> psub & sub %~ IM.insert (fromIntegral x) pv
  Just oldpv -> case runState (merge oldpv pv) (psub^.isLinear) of
    (pv, isLin) -> psub & sub %~ IM.insert (fromIntegral x) pv
                        & isLinear .~ isLin

updatePSub0 :: PartialSub -> Lvl -> PartialVal0 -> PartialSub
updatePSub0 psub x (PSEVal0 -> pv) = case IM.lookup (fromIntegral x) (psub^.sub) of
  Nothing    -> psub & sub %~ IM.insert (fromIntegral x) pv
  Just oldpv -> case runState (merge oldpv pv) (psub^.isLinear) of
    (pv, isLin) -> psub & sub %~ IM.insert (fromIntegral x) pv
                        & isLinear .~ isLin

-- Partial substitution
----------------------------------------------------------------------------------------------------

data RevSpine
  = RSId
  | RSApp Val Icit RevSpine
  | RSProject Proj RevSpine
  deriving Show

reverseSpine :: Spine -> RevSpine
reverseSpine = go RSId where
  go acc SId            = acc
  go acc (SApp t u i)   = go (RSApp u i acc) t
  go acc (SProject t p) = go (RSProject p acc) t

class PSubst a b | a -> b where
  psubst :: PSubArg => a -> b

psubstIn :: PSubst a b => PartialSub -> a -> b
psubstIn psub a = setPSub psub (psubst a)

instance PSubst Spine (Tm -> IO Tm) where
  psubst t hd = case t of
    SId          -> pure hd
    SApp t u i   -> S.App ! psubst t hd ∙ psubst u ∙ pure i
    SProject t p -> S.Project ! psubst t hd ∙ pure p

instance PSubst RevSpine (Tm -> IO Tm) where
  psubst sp acc = case sp of
    RSId           -> pure acc
    RSApp t i sp   -> do t <- psubst t; psubst sp (S.App acc t i)
    RSProject p sp -> psubst sp (S.Project acc p)

instance PSubst Env (IO S.MetaSub) where
  psubst e = S.MSSub ! go e where
    go :: PSubArg => Env -> IO S.TmEnv
    go = \case
      ENil       -> pure S.TENil
      EDef   e v -> S.TEDef   ! go e ∙ psubst v
      EBind  e v -> S.TEBind  ! go e ∙ psubst v
      EBind0 e v -> S.TEBind0 ! go e ∙ psubst v

instance ReadBack PartialRecFields (Tm -> [Val] -> IO Tm) where
  readb pvs hd args = case pvs of
    PRFNil          -> pure hd
    PRFSnoc pvs t i -> S.App ! readb pvs hd args ∙ readb t args ∙ pure i

instance ReadBack PartialVal ([Val] -> IO Tm) where
  readb pv args = case pv of
    PVTotal v      -> pure $! readb (v ∙ args)
    PVTop          -> unifyError
    PVBot          -> unifyError
    PVLam x i a pv -> let va = a ∙ args in
                      S.Lam . BindI x i (readb va) ! fresh va \v -> readb pv (v:args)
    PVRec i pvs    -> readb pvs (S.Rec i) args
    PVQuote pv     -> S.quote ! readb pv

instance ReadBack PartialVal0 (IO Tm0) where
  readb = \case
    PV0Total v     -> pure $! readb v
    PV0Top; PV0Bot -> unifyError

applyPVal :: PSubArg => PartialVal -> RevSpine -> [Val] -> IO Tm
applyPVal pv sp args = case (pv, sp) of
  (PVLam a _ _ pv, RSApp t i sp  ) -> do t <- psubst t
                                         applyPVal pv sp (evalInDom t : args)
  (PVRec i pvs   , RSProject p sp) -> applyPVal (elemAt pvs (p^.index)) sp args
  (PVTotal v     , sp            ) -> psubst sp (readBackNoUnfold (?psub^.dom) (setLvl (?psub^.dom) (v ∙ args)))
  (pv            , RSId          ) -> setUnfold UnfoldNone $ readbInDom pv args
  _                                -> unifyError

unsolvedMetaOccurs :: PSubArg => MetaVar -> IO ()
unsolvedMetaOccurs m = case ?psub^.occurs of
  Just m' | m == m' -> unifyError
  _ -> pure ()

solvedMetaOccurs :: PSubArg => MetaVar -> IO ()
solvedMetaOccurs m = case ?psub^.occurs of
  Just m' -> do

    let goMeta :: MetaVar -> IO ()
        goMeta m = case ES.lookupMeta m of
          ES.MESolved e -> do
            cached <- RF.read (e^.ES.occursCache)
            when (cached /= m') do
              goTm (e^.solution)
              RF.write (e^.ES.occursCache) m'
          ES.MESolved0 e -> do
            cached <- RF.read (e^.ES.occursCache)
            when (cached /= m') do
              goTm0 (e^.solution)
              RF.write (e^.ES.occursCache) m'
          ES.MEUnsolved e ->
            if m == m' then unifyError else pure ()

        goTm :: Tm -> IO ()
        goTm = \case
          S.LocalVar{};S.TCon{};S.DCon{};S.Rec{};S.RecTy{};S.TopDef{};S.Prim{}
            -> pure ()
          S.Meta m s    -> goMeta m >> goMetaSub s
          S.Let t u     -> goTm t >> goTm (u^.ty) >> goTm (u^.body)
          S.Pi b        -> goTm (b^.ty) >> goTm (b^.body)
          S.App t u _   -> goTm t >> goTm u
          S.Lam t       -> goTm (t^.ty) >> goTm (t^.body)
          S.Project t _ -> goTm t
          S.Quote t     -> goTm0 t
          S.Wk t        -> goTm t
          S.Coe a b t   -> goTm a >> goTm b >> goTm t

        goTm0 :: Tm0 -> IO ()
        goTm0 = \case
          S.LocalVar0{};S.DCon0{};S.TopDef0{};S.Rec0{} -> pure ()
          S.Meta0 m e    -> goMeta m >> goMetaSub e
          S.Project0 t _ -> goTm0 t
          S.CProject t _ -> goTm0 t
          S.App0 t u     -> goTm0 t >> goTm0 u
          S.Lam0 t       -> goTm (t^.ty) >> goTm0 (t^.body)
          S.Let0 t u     -> goTm0 t >> goTm (u^.ty) >> goTm0 (u^.body)
          S.Decl0 t      -> goTm (t^.ty) >> goTm0 (t^.body)
          S.Splice t     -> goTm t

        goMetaSub :: S.MetaSub -> IO ()
        goMetaSub = \case
          S.MSId    -> pure ()
          S.MSSub s -> goTmEnv s

        goTmEnv :: S.TmEnv -> IO ()
        goTmEnv = \case
          S.TENil       -> pure ()
          S.TEDef e t   -> goTmEnv e >> goTm t
          S.TEBind e t  -> goTmEnv e >> goTm t
          S.TEBind0 e t -> goTmEnv e >> goTm0 t

    case ES.lookupMeta m of
      ES.MESolved e   -> goTm (e^.solution)
      ES.MESolved0 e  -> goTm0 (e^.solution)
      ES.MEUnsolved e -> impossible

  _ -> pure ()

psubstLvl :: PSubArg => Lvl -> IO PartialVal
psubstLvl x = case IM.lookup (fromIntegral x) (?psub^.sub) of
  Nothing         -> unifyError
  Just (PSEVal v) -> pure v
  _               -> impossible

psubstLvl0 :: PSubArg => Lvl -> IO PartialVal0
psubstLvl0 x = case IM.lookup (fromIntegral x) (?psub^.sub) of
  Nothing          -> unifyError
  Just (PSEVal0 v) -> pure v
  _                -> impossible

instance PSubst ClosureI (IO (BindI Tm)) where
  psubst (ClI x i a t) = do
    a' <- psubst a
    BindI x i a' ! psubstIn (lift (evalInDom a') ?psub)
                            (setLvl (?psub^.cod + 1) (t (LocalVar (?psub^.cod) a)))

instance PSubst Val (IO Tm) where
  psubst v = case forceInCod v of
    Rigid h sp -> case h of
      RHLocalVar x a -> do v <- psubstLvl x; applyPVal v (reverseSpine sp) []
      RHPrim i       -> psubst sp (S.Prim i)
      RHDCon i       -> psubst sp (S.DCon i)
      RHTCon i       -> psubst sp (S.TCon i)
      RHRecTy i      -> psubst sp (S.RecTy i)
      RHRec i        -> psubst sp (S.Rec i)

    -- TODO: pruning
    Flex (MetaHead m e) sp -> do
      unsolvedMetaOccurs m
      hd <- S.Meta m ! psubst e
      psubst sp hd

    Unfold h sp v -> do
      let goHead = case h of
            UHMeta (MetaHead m e) -> solvedMetaOccurs m *> (S.Meta m ! psubst e)
            UHTopDef i            -> pure $ S.TopDef i
            UHLocalDef x _        -> do v <- psubstLvl x; applyPVal v (reverseSpine sp) []
      (psubst sp =<< goHead) `catchUnify` psubst v

    Pi b    -> S.Pi ! psubst b
    Lam t   -> S.Lam ! psubst t
    Quote t -> S.Quote ! psubst t

instance PSubst Closure0 (IO (Bind Tm0)) where
  psubst (Cl0 x a f) =
    Bind x ! psubst a
           ∙ setPSub (lift0 ?psub) (setLvl (?psub^.cod + 1) (psubst (f (LocalVar0 (?psub^.cod)))))

psubstMetaHead0 :: PSubArg => MetaHead -> IO S.Tm0
psubstMetaHead0 (MetaHead m e) = do
  unsolvedMetaOccurs m
  S.Meta0 m ! psubst e

instance PSubst Spine0 (Tm0 -> IO Tm0) where
  psubst sp hd = case sp of
    S0Id            -> pure hd
    S0CProject sp p -> S.CProject ! psubst sp hd ∙ pure p

instance PSubst (SnocList Val0) (Tm0 -> IO Tm0) where
  psubst sp hd = case sp of
    Nil       -> pure hd
    Snoc sp v -> S.App0 ! psubst sp hd ∙ psubst v

instance PSubst Val0 (IO Tm0) where
  psubst t = case force0InCod t of
    Unfold0 m sp v -> (psubst sp =<< psubstMetaHead0 m) `catchUnify` psubst v
    Rigid0 v sp    -> psubst sp =<< psubst v
    Flex0 m sp     -> psubst sp =<< psubstMetaHead0 m
    LocalVar0 x    -> do v <- psubstLvl0 x; setLvl (?psub^.dom) $ setUnfold UnfoldNone $ readb v
    Splice v sp    -> psubst sp =<< (S.splice ! psubst v)
    TopDef0 i      -> pure $ S.TopDef0 i
    DCon0 i        -> pure $ S.DCon0 i
    App0 t u       -> S.App0 ! psubst t ∙ psubst u
    Lam0 t         -> S.Lam0 ! psubst t
    Decl0 t        -> S.Decl0 ! psubst t
    Project0 t p   -> S.Project0 ! psubst t ∙ pure p
    Let0 t u       -> S.Let0 ! psubst t ∙ psubst u
    CRec i vs      -> psubst vs (S.Rec0 i)
    Rec0 i         -> pure $ S.Rec0 i


-- Nested solving
----------------------------------------------------------------------------------------------------

data RevSpine'
  = RSId'
  | RSApp' Val (Name, Icit, VTy) RevSpine' -- arg val, Pi dom info
  | RSProject' Proj (RecInfo, Spine) RevSpine' -- proj, Rec type info
  deriving Show

reverseSpine' :: LvlArg => (Spine -> Val) -> VTy -> Spine -> RevSpine'
reverseSpine' hd ~a sp = snd (go sp) where
  go :: Spine -> (VTy, RevSpine')
  go SId           = (a, RSId')
  go (SApp sp t i) = case go sp of
    (a, rsp) -> case appTy a t of
      (x, i, tty, a) -> (a, RSApp' t (x, i, tty) rsp)
  go (SProject sp p) = case go sp of
    (a, rsp) -> case hd sp of
      v -> case projTy v a p of
        (inf, params, a) -> (a, RSProject' p (inf, params) rsp)

data RevSpine'' = RevSpine'' {
    revSpine''LhsTy       :: VTy
  , revSpine''LhsMetaHead :: {-# nounpack #-} MetaHead
  , revSpine''LhsSpine    :: Spine
  , revSpine''DomLocals   :: S.Locals
  , revSpine''RhsSpine    :: RevSpine
  }
makeFields ''RevSpine''

-- data Spine0 = S0Splice Spine | S0Id deriving (Show)

-- invertVal0 :: Lvl -> PartialSub -> Lvl -> Val0 -> Spine0 -> IO PartialSub
-- invertVal0 solvable psub param t rhsSp = case whnf0 t of
--   LocalVar0 x -> do
--     -- NOTE the "param == psub^.cod"
--     -- This enforces that the rhsSp can only contain projections
--     -- Otherwise we can't hope to solve, since the LHS is an object expression, so it can never be
--     -- applied to invertible args. On the other hand, a spine that only contains projections can
--     -- be trivially plugged into the solution.
--     unless (solvable <= x && x < psub^.cod && param == psub^.cod) unifyError
--     pure $! updatePSub0 psub x $ PV0Total $ case (rhsSp, psub^.domEnv) of
--       (S0Id          , EBind0 _ v              ) -> v
--       (S0Splice rhsSp, EBind _ (LocalDef y a v)) -> Splice $ Rigid (RHLocalVar y a) rhsSp
--       _                                          -> impossible

--   Splice (whnf -> Rigid rh@(RHLocalVar x a) sp) -> do
--     case rhsSp of S0Id -> pure (); _ -> impossible
--     unless (solvable <= x && x < psub^.cod) unifyError
--     let rsp = reverseSpine' (Rigid rh) a sp
--     pv <- solveNestedSp (psub^.domEnv) (psub^.cod) psub rsp SId
--     pure $! updatePSub psub x pv

--   _  -> unifyError

invertVal :: Lvl -> PartialSub -> Lvl -> Val -> Spine -> IO PartialSub
invertVal solvable psub param t rhsSp = do
  debug ["INVERTVAL", show t, show rhsSp]
  setLvl param (whnfIO t) >>= \case
    Lam t -> do
      let var = LocalVar param (t^.ty)
      invertVal solvable psub (param + 1) (setLvl param (t ∙ var))
                (SApp rhsSp var (t^.icit))

    Quote t -> do
      impossible

    Rigid (RHRec i) sp -> do

      let go :: PartialSub -> FieldInfo -> Spine -> Ix -> IO PartialSub
          go psub fs sp ix = case (fs, sp) of
            (FINil, SId                  ) -> pure psub
            (FISnoc fs x i a, SApp sp t _) -> do
              psub <- go psub fs sp (ix + 1)
              invertVal solvable psub param t (SProject rhsSp (Proj ix x))
            _ -> impossible

      go psub (i^.fields) sp 0

    Rigid rh@(RHLocalVar x a) sp -> do
      debug ["INVERTVAR", show solvable, show x, show (psub^.cod), show sp, setLvl param (show $ readbNoUnfold a)]
      unless (solvable <= x && x < psub^.cod) (inversionError psub)
      let rsp = setLvl param $ reverseSpine' (Rigid rh) a sp
      debug ["KEK"]
      let psub' = psub & cod .~ param
      res <- updatePSub psub x ! solveNestedSp (psub^.domEnv) (psub^.cod) psub' rsp rhsSp
      -- debug ["INVERTED VAR"]
      pure res


    _ -> inversionError psub

-- | Invert value and catch inversion exceptions.
topInvertVal :: PartialSub -> Lvl -> Val -> Spine -> IO PartialSub
topInvertVal psub param t rhsSp =
  invertVal 0 psub param t rhsSp `catch` \(_ :: InversionEx) -> unifyError

makeMCl :: Env -> Tm -> MultiClosure Val
makeMCl rootEnv t = MCl \args -> evalE (foldl' EDef rootEnv args) t

solveNestedSp :: Env -> Lvl -> PartialSub -> RevSpine' -> Spine -> IO PartialVal
solveNestedSp rootEnv solvable psub rsp rhsSp = do
  debug ["SOLVE NESTED", show solvable, show rsp, show rhsSp]
  case rsp of
    RSId' -> do
      let hd = case rootEnv of
            EBind _ (LocalVar x a) -> S.LocalVar (lvlToIx (psub^.dom) x)
            _                      -> impossible
      body <- psubstIn psub rhsSp hd
      pure $! PVTotal (makeMCl rootEnv body)

    RSApp' u (x, i, a) rsp -> do
      a <- psubstIn psub a
      let ~va = setPSub psub $ evalInDom a
      let d = psub^.dom
      let var = LocalVar d va
      psub <- invertVal solvable (psub & domEnv %~ (`EBind` var) & dom +~ 1) (psub^.cod) u SId
      pv <- solveNestedSp rootEnv solvable psub rsp rhsSp
      pure $! PVLam x i (makeMCl rootEnv a) pv

    RSProject' p (inf, params) rsp -> do
      pv <- solveNestedSp rootEnv solvable psub rsp rhsSp

      let mkFields :: FieldInfo -> Ix -> PartialRecFields
          mkFields fs ix = case (fs, ix) of
            (FISnoc fs _ i _, 0 ) -> PRFSnoc (bottoms fs) pv i
            (FISnoc fs _ i _, ix) -> PRFSnoc (mkFields fs (ix - 1)) PVBot i
            _                     -> impossible

          bottoms :: FieldInfo -> PartialRecFields
          bottoms = \case
            FINil           -> PRFNil
            FISnoc fs _ i _ -> PRFSnoc (bottoms fs) PVBot i

      pure $! PVRec inf (mkFields (inf^.fields) (p^.index))


-- Top solving
----------------------------------------------------------------------------------------------------


-- | "Reverse environment" annotated with everything that we need to invert the Env.
data RevEnv
  = RENil
  | REDef   Name Tm  ~Val  Ty ~VTy RevEnv -- dom Tm, cod Val,  dom Ty, cod VTy
  | REBind  Name     ~Val  Ty ~VTy RevEnv --         cod Val,  dom Ty, cod VTy
  | REBind0 Name     ~Val0 Ty ~VTy RevEnv --         cod Val0, dom Ty, cod VTy

reverseEnv :: LvlArg => S.Locals -> Env -> RevEnv
reverseEnv ls e = go ls e RENil where
  go :: LvlArg => S.Locals -> Env -> RevEnv -> RevEnv
  go ls e acc = case (ls, e) of
    (S.LNil         , ENil      ) -> acc
    (S.LDef ls x t a, EDef e v  ) -> go ls e (REDef   x t v a (evalE e a) acc)
    (S.LBind ls x a , EBind e v ) -> go ls e (REBind  x v a   (evalE e a) acc)
    (S.LBind0 ls x a, EBind0 e v) -> go ls e (REBind0 x v a   (evalE e a) acc)
    _                             -> impossible

solveTopMetaSub ::
     PartialSub  -- ^ Partial substitution from dom to cod
  -> Env         -- ^ Original Env in "(MetaVar, Env) Spine =? Rhs"
  -> RevEnv      -- ^ Reversed Env
  -> Spine       -- ^ Rhs spine
  -> Val         -- ^ Rhs value
  -> IO S.Tm
solveTopMetaSub psub lhsEnv renv sp rhs = case renv of
  RENil -> do

    (m, lhsTy, locals) <- case psub^.occurs of
      Just m -> do inf <- ES.lookupUnsolved m
                   let ~vty = evalLE (psub^.cod) lhsEnv (inf^.ty)
                   pure (m, vty, inf^.locals)
      _      -> impossible

    solveTopSpine psub (reverseSpine'' lhsTy (MetaHead m lhsEnv) SId locals sp) rhs

    -- It only makes sense to map local defs to local defs. We don't need to worry about beta-eta
    -- stability, because local def inversion is purely an optimization and it's transparent to
    -- conversion. If we don't have the localdef->localdef renaming, we just continue and unfold
    -- the codomain definition subsequently in the output.
  REDef x t codvt a _ renv -> do

    let domVar = setPSub psub $ LocalDef (psub^.dom) (evalInDom a) (evalInDom t)
    psub <- pure $ psub & dom +~ 1 & domEnv %~ (`EDef` domVar)

    case setPSub psub $ forceInCod codvt of
      LocalDef x _ _ -> do
        entry <- handle @UnifyEx (\_ -> pure PVTop) do
          unless (psub^.isLinear) (() <$ psubstIn psub codvt)
          pure $ PVTotal $ MCl \_ -> domVar
        solveTopMetaSub (updatePSub psub x entry) lhsEnv renv sp rhs
      _ -> do
        solveTopMetaSub psub lhsEnv renv sp rhs

  -- checks: 1) arg is invertible 2) if psubst is nonlinear, problem-scope binder *type* is psubst-able
  --         we block/fail if either fails
  REBind x codv a codva renv -> do
    let domVar = setPSub psub $ LocalVar (psub^.dom) (evalInDom a)
    psub <- pure $ psub & dom +~ 1 & domEnv %~ (`EBind` domVar)
    psub <- topInvertVal psub (psub^.cod) codv SId
    unless (psub^.isLinear) (() <$ psubstIn psub codva)
    solveTopMetaSub psub lhsEnv renv sp rhs

  REBind0 x codv a codva renv ->
    impossible

reverseSpine'' :: VTy -> MetaHead -> Spine -> S.Locals -> Spine -> RevSpine''
reverseSpine'' lhsTy lhsHd lhsSp ls sp =
  RevSpine'' lhsTy lhsHd lhsSp ls (reverseSpine sp)

solveTopSpine :: PartialSub -> RevSpine'' -> Val -> IO Tm
solveTopSpine psub rsp rhs = case rsp^.rhsSpine of
  RSId ->
    psubstIn psub rhs

  RSApp argv i rhsSp -> do
    let ((`pickName` x_) -> x , _, codva, appty) = setLvl (psub^.cod) $ appTy (rsp^.lhsTy) argv
    a <- psubstIn psub codva
    let domVar = setPSub psub $ LocalVar (psub^.dom) (evalInDom a)
    psub <- topInvertVal (psub & domEnv %~ (`EBind` domVar) & dom +~ 1) (psub^.cod) argv SId
    let rsp' = RevSpine'' appty (rsp^.lhsMetaHead)
                                (SApp (rsp^.lhsSpine) argv i)
                                (S.LBind (rsp^.domLocals) x a)
                                rhsSp
    S.Lam . BindI x i a ! solveTopSpine psub rsp' rhs

  RSProject p rhsSp -> do

    (info, params) <- setLvl (psub^.cod) (whnfIO (rsp^.lhsTy)) >>= \case
      RecTy info params -> pure (info,params)
      _                 -> impossible

    let go :: Ix -> FieldInfo -> IO (Env, Tm)
        go ix = \case
          FINil ->
            pure $! recParamEnv params // S.Rec info
          FISnoc fields x i a -> do
            (codenv, t) <- go (ix - 1) fields
            let codva = evalLE (psub^.cod) codenv a
            a <- psubstIn psub codva
            let lhsSp    = SProject (rsp^.lhsSpine) (Proj ix x)
            let codprojv = Flex (rsp^.lhsMetaHead) lhsSp
            let codenv'  = EBind codenv codprojv
            if ix == p^.index then do
              let rsp' = rsp & lhsTy .~ codva & rhsSpine .~ rhsSp & lhsSpine .~ lhsSp
              u <- solveTopSpine psub rsp' rhs
              pure (codenv', S.App t u i)
            else do
              u <- S.setLocals (rsp^.domLocals) (freshMeta a)
              pure (codenv', S.App t u i)

    snd ! go 0 (info^.fields)

----------------------------------------------------------------------------------------------------

data UnifyState
  = USPrecise Int   -- ^ We're computing everything precisely. We have Int amount
                    --   of fule for speculation.
  | USSpeculating   -- ^ We're speculating on one or more definition unfolding.
                    --   We can't unfold any new definition and can't solve metas.
  deriving (Eq, Show)

type UnifyStateArg = (?unifyState :: UnifyState)

{-# inline setUnifyState #-}
setUnifyState :: UnifyState -> (UnifyStateArg => a) -> a
setUnifyState s act = let ?unifyState = s in act

forceUS :: UnifyStateArg => LvlArg => Val -> Val
forceUS v = case ?unifyState of
  USPrecise 0 -> whnf v
  _           -> force v

unifyEq :: Eq a => a -> a -> IO ()
unifyEq a a' = if a == a' then pure () else unifyError

type DoUnify a = LvlArg => UnifyStateArg => LocalsArg => a

class Unify a where
  unify :: DoUnify (a -> a -> IO ())

instance Unify RigidHead where
  unify = unifyEq

instance Unify Proj where
  unify p p' = unifyEq (p^.index) (p'^.index)

instance Unify Val where
  unify t t' = unify (gjoin t) (gjoin t')

instance Unify Spine where
  unify sp sp' = case (sp, sp') of
    (SId          , SId            ) -> pure ()
    (SApp sp t _  , SApp sp' t' _  ) -> do unify sp sp'; unify t t'
    (SProject sp p, SProject sp' p') -> do unify sp sp'; unify p p'
    _                                -> unifyError

instance Unify ClosureI where
  unify t t' = do
    unify (t^.ty) (t'^.ty)
    fresh (t^.ty) \x ->
      let ?locals = S.LBind ?locals (t^.name) (readbNoUnfold (t^.ty))
      in unify (t ∙ x) (t' ∙ x)

instance Unify Val0 where
  unify = impossible

-- Only in speculative unification!
instance Unify MetaHead where
  unify (MetaHead m e) (MetaHead m' e') = do unifyEq m m'; unify e e'

-- Only in Speculative unification!
instance Unify UnfoldHead where
  unify h h' = case (h, h') of
    (UHMeta m      , UHMeta m'      ) -> unify m m'
    (UHTopDef i    , UHTopDef i'    ) -> unifyEq i i'
    (UHLocalDef x _, UHLocalDef x' _) -> unifyEq x x'
    _                                 -> unifyError

instance Unify Env where
  unify e e' = case (e, e') of
    (ENil     , ENil       ) -> pure ()
    (EDef e _ , EDef e' _  ) -> unify e e'
    (EBind e t, EBind e' t') -> do unify e e'; unify t t'
    (EBind0{} , EBind0{}   ) -> impossible
    _                        -> impossible

instance (Unify a, Unify b) => Unify (a, b) where
  {-# inline unify #-}
  unify (a, b) (a', b') = unify a a' >> unify b b'

-- TODO: this changes unification orientation, have 2 copies or pass a direction argument
-- TODO: disallow unit eta case
recordEta :: DoUnify (RecInfo -> Spine -> G -> IO ())
recordEta i sp v = go (i^.fields) sp 0 where
  go :: FieldInfo -> Spine -> Ix -> IO ()
  go fs sp ix = case (fs, sp) of
    (FINil, SId)                   -> pure ()
    (FISnoc fs x i a, SApp sp t _) -> do
      unify (gjoin t) (gproj v (Proj ix x))
      go fs sp (ix - 1)
    _ -> impossible

solve :: DoUnify (MetaHead -> Spine -> Val -> IO ())
solve (MetaHead m e) sp rhs = do

  debug ["SOLVE", prettyReadb (Flex (MetaHead m e) sp), prettyReadb rhs]

  frozen <- ES.isFrozen m
  when (frozen || ?unifyState == USSpeculating) unifyError

  let psub = PSub (Just m) False True ENil 0 ?lvl mempty
  ES.Unsolved ls a blocking <- ES.lookupUnsolved m
  sol <- solveTopMetaSub psub e (reverseEnv ls e) sp rhs
  ES.newSolution m ls a sol

  debug ["SOLVED", prettyReadb (Flex (MetaHead m e) sp), show blocking, show sol]
  debug ["PRETTY SOL", pretty sol]

  IS.foldr (\i act -> retryProblem i >> act) (pure ()) blocking

-- | Try to solve a meta without eta expansions. This can fail by spurious occurs checking. If it
--   fails, we retry with eta expansion. We don't have to backtrack metastate updates because
--   everything should be stable under eta.
solveEtaShort :: DoUnify (MetaHead -> Spine -> Val -> IO ())
solveEtaShort m sp rhs = do
  -- debug ["SOLVEETASHORT", show m, prettyReadb rhs]
  -- TODO: should only backtrack from occurs checks of "m", otherwise the eta expansion doesn't
  -- help and we're better off postponing
  solve m sp rhs `catchUnify` solveEtaLong m sp rhs

-- TODO: disallow unit eta case
solveEtaLongRec :: LvlArg => UnifyStateArg => MetaHead -> Spine -> RecInfo -> Spine -> IO ()
solveEtaLongRec m sp inf args = go (inf^.fields) 0 args where
  go :: FieldInfo -> Ix -> Spine -> IO ()
  go fs ix args = case (fs, args) of
    (FINil, SId) -> pure ()
    (FISnoc fs x i a, SApp args t _) -> do
      let p = Proj ix x
      solveEtaLongRec m (SProject sp p) inf args
      go fs (ix - 1) args
    _ -> impossible


solveEtaLong :: DoUnify (MetaHead -> Spine -> Val -> IO ())
solveEtaLong m sp rhs = whnfIO rhs >>= \case
  Lam t    -> fresh (t^.ty) \x -> solveEtaLong m (SApp sp x (t^.icit)) (t ∙ x)
  Rec i ts -> solveEtaLongRec m sp i ts
  rhs      -> solve m sp rhs


-- | We try to solve the newer metas first, to minimize the number of scope-escaping metas.
--   IMPORTANT: we only backtrack from the current spine inversion, which is OK because
--   inversion does not modify metastate. We can't simply backtrack from partial substitution,
--   because it can trigger pruning and retry arbitrary constraints.
--
--   TODO: ideally, if both spines are invertible, then both spines should be also partial subst-able
--   with pruning, so there should be no point trying to backtrack from partial subst. However,
--   this requires that pruning is at least as smart as inversion, so it can handle all invertible
--   values, which is not going to be the case for a while.

flexFlex :: DoUnify (MetaHead -> Spine -> Val -> MetaHead -> Spine -> Val -> IO ())
flexFlex mh@(MetaHead m e) sp topt mh'@(MetaHead m' e') sp' topt' = case compare m m' of
  LT -> solve mh' sp' topt `catch` \case
          InversionEx m'' | m'' == m' -> solve mh sp topt'
          ex -> throwIO ex
  GT -> solve mh sp topt' `catch` \case
          InversionEx m'' | m'' == m -> solve mh' sp' topt
          ex -> throwIO ex
  -- TODO: try to intersect
  --       spine unification should not be a hard fail
  EQ -> unify (e, sp) (e', sp')

lopsidedUnfold :: DoUnify (G -> G -> IO ())
lopsidedUnfold g g' = case ?unifyState of
  USPrecise{}   -> unify g g'
  USSpeculating -> unifyError

instance Unify G where
  unify (G topt ftopt) (G topt' ftopt') = do
    debug ["GOUNIFY", prettyReadb topt, prettyReadb topt']
    -- debug ["GOUNIFY", show topt, show topt']

    case forceUS ftopt // forceUS ftopt' of
      -- matching sides
      (Rigid h sp, Rigid h' sp') -> unify (h, sp) (h', sp')
      (Pi b      , Pi b'       ) -> unify b b'
      (Lam t     , Lam t'      ) -> unify t t'
      (Quote t   , Quote t'    ) -> unify t t'

      -- unfoldings
      (Unfold h sp v, Unfold h' sp' v') -> case ?unifyState of
        USPrecise n   -> setUnifyState USSpeculating (unify h h' >> unify sp sp')
                         `catchUnify`
                         setUnifyState (USPrecise (n - 1)) (unify (G topt v) (G topt' v'))
        USSpeculating -> unify (h, sp) (h', sp')

      -- eta-short meta solutions
      (Flex m sp, Flex m' sp') -> flexFlex m sp topt m' sp' topt'
      (Flex m sp, t'         ) -> solveEtaShort m sp topt'
      (t        , Flex m' sp') -> solveEtaShort m' sp' topt

      -- lopsided unfolding
      (Unfold _ _ t, t') -> lopsidedUnfold (G topt t) (G topt' t')
      (t, Unfold _ _ t') -> lopsidedUnfold (G topt t) (G topt' t')

      -- syntax-directed eta
      (Lam t, t') -> fresh (t^.ty) \x -> let arg = (x, t^.icit) in
                     unify (G (topt ∙∘ arg) (t ∙ x)) (G (topt' ∙∘ arg) (t' ∙∘ arg))
      (t, Lam t') -> fresh (t'^.ty) \x -> let arg = (x, t'^.icit) in
                     unify (G (topt ∙∘ arg) (t ∙∘ arg)) (G (topt' ∙∘ arg) (t' ∙ x))

      (Rec i sp, t')  -> recordEta i sp (G topt' t')
      (t, Rec i' sp') -> recordEta i' sp' (G topt t)

      _ -> unifyError

----------------------------------------------------------------------------------------------------
