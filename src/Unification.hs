{-# options_ghc -Wno-unused-imports #-}

module Unification where

import Common
import Core.Info
import Core.Syntax (Ty, Tm, Locals, LocalsArg, Tm0)
import qualified Core.Syntax as S
import Core.Value
import qualified Elaboration.State as ES

import Evaluation
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM


----------------------------------------------------------------------------------------------------

freshMeta :: LocalsArg => Ty -> IO Tm
freshMeta a = S.Meta ! ES.newMeta a ∙ pure S.MSId

data UnifyEx = UETodo deriving Show
instance Exception UnifyEx

unifyError :: Dbg => IO a
unifyError = throwIO UETodo


-- Partial Substitutions
----------------------------------------------------------------------------------------------------

newtype MultiClosure a = MCl ([Val] -> a)
instance Show (MultiClosure a) where show _ = "<closure>"
instance Apply (MultiClosure Val) [Val] Val where
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
  , partialSubDomEnv       :: Env              -- ^ Identity environment for the domain
  , partialSubDom          :: Lvl              -- ^ Domain (size of the map)
  , partialSubCod          :: Lvl              -- ^ Codomain (next fresh Lvl)
  , partialSubSub          :: IntMap PSubEntry -- ^ Map from codomain vars to partial values.
                                               --   Missing entries are Bot.
  }
makeFields ''PartialSub

type PSubArg = (?psub :: PartialSub)

setPSub :: PartialSub -> (PSubArg => a) -> a
setPSub s act = let ?psub = s in act

instance Semigroup PartialRecFields where
  PRFNil         <> PRFNil         = PRFNil
  PRFSnoc ts t i <> PRFSnoc us u _ = PRFSnoc (ts <> us) (t <> u) i
  _              <> _              = impossible

instance Semigroup PartialVal where
  PVBot         <> u             = u
  t             <> PVBot         = t
  PVLam x i a t <> PVLam _ _ _ u = PVLam x i a (t <> u)
  PVRec i ts    <> PVRec _ us    = PVRec i (ts <> us)
  _             <> _             = PVTop

instance Semigroup PartialVal0 where
  PV0Bot <> u      = u
  t      <> PV0Bot = t
  _      <> _      = PV0Top

instance Semigroup PSubEntry where
  PSEVal  pv <> PSEVal  pv' = PSEVal  (pv <> pv')
  PSEVal0 pv <> PSEVal0 pv' = PSEVal0 (pv <> pv')
  _          <> _           = impossible

lift :: VTy -> PartialSub -> PartialSub
lift ~a (PSub occ pr idenv dom cod sub) =
  let var = LocalVar dom a in
  PSub occ pr (EDef idenv var) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PSEVal (PVTotal (MCl \_ -> var))) sub

lift0 :: PartialSub -> PartialSub
lift0 (PSub occ pr idenv dom cod sub) =
  let var = LocalVar0 dom in
  PSub occ pr (EBind0 idenv var) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PSEVal0 (PV0Total var)) sub

updatePSub :: PartialSub -> Lvl -> PartialVal -> PartialSub
updatePSub psub x pv = psub & sub %~ IM.insertWith (<>) (fromIntegral x) (PSEVal pv)

updatePSub0 :: PartialSub -> Lvl -> PartialVal0 -> PartialSub
updatePSub0 psub x pv = psub & sub %~ IM.insertWith (<>) (fromIntegral x) (PSEVal0 pv)


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

instance ReadBack PartialVal0 (IO Tm0) where
  readb = \case
    PV0Total v     -> pure $! readb v
    PV0Top; PV0Bot -> unifyError

applyPVal :: PSubArg => PartialVal -> RevSpine -> [Val] -> IO Tm
applyPVal pv sp args = case (pv, sp) of
  (PVLam a _ _ pv, RSApp t i sp  ) -> do t <- psubst t
                                         applyPVal pv sp (evalIn (?psub^.domEnv) t : args)
  (PVRec i pvs   , RSProject p sp) -> applyPVal (elemAt pvs (p^.index)) sp args
  (PVTotal v     , sp            ) -> psubst sp (readBackNoUnfold (?psub^.dom) (v ∙ args))
  (pv            , RSId          ) -> setLvl (?psub^.dom) $ setUnfold UnfoldNone $ readb pv args
  _                                -> unifyError

approxOccursInMeta :: MetaVar -> MetaVar -> IO ()
approxOccursInMeta occ m = error "TODO"

checkMetaOccurs :: PSubArg => MetaVar -> IO ()
checkMetaOccurs m = case ?psub^.occurs of
  Just m' -> when (m == m') unifyError
  _       -> pure ()

psubstLvl :: PSubArg => Lvl -> PartialVal
psubstLvl x = case (?psub^.sub) IM.! fromIntegral x of
  PSEVal v -> v
  _        -> impossible

psubstLvl0 :: PSubArg => Lvl -> PartialVal0
psubstLvl0 x = case (?psub^.sub) IM.! fromIntegral x of
  PSEVal0 v -> v
  _         -> impossible

instance PSubst ClosureI (IO (BindI Tm)) where
  psubst (ClI x i a t) = do
    a' <- psubst a
    BindI x i a' ! psubstIn (lift (evalIn (?psub^.domEnv) a') ?psub)
                            (t (LocalVar (?psub^.cod) a))

instance PSubst Val (IO Tm) where
  psubst v = case force v of
    Rigid h sp -> case h of
      RHLocalVar x a -> applyPVal (psubstLvl x) (reverseSpine sp) []
      RHPrim i       -> psubst sp (S.Prim i)
      RHDCon i       -> psubst sp (S.DCon i)
      RHTCon i       -> psubst sp (S.TCon i)
      RHRecTy i      -> psubst sp (S.RecTy i)
      RHRec i        -> psubst sp (S.Rec i)

    -- TODO: pruning
    Flex (MetaHead m e) sp -> do
      checkMetaOccurs m
      hd <- S.Meta m ! psubst e
      psubst sp hd

    Unfold h sp v -> do
      let goHead = case h of
            UHMeta (MetaHead m e) -> checkMetaOccurs m *> S.Meta m ! psubst e
            UHTopDef i            -> pure $ S.TopDef i
            UHLocalDef x _        -> applyPVal (psubstLvl x) (reverseSpine sp) []
      catch @UnifyEx (psubst sp =<< goHead) \_ -> psubst v

    Pi b    -> S.Pi ! psubst b
    Lam t   -> S.Lam ! psubst t
    Quote t -> S.Quote ! psubst t

instance PSubst Closure0 (IO (Bind Tm0)) where
  psubst (Cl0 x a f) =
    Bind x ! psubst a ∙ setPSub (lift0 ?psub) (psubst (f (LocalVar0 (?psub^.cod))))

instance PSubst Val0 (IO Tm0) where
  psubst t = case force0 t of
    LocalVar0 x                  -> setLvl (?psub^.dom) $ setUnfold UnfoldNone $ readb $ psubstLvl0 x
    Meta0 (MetaHead m e)         -> checkMetaOccurs m *> S.Meta0 m ! psubst e
    SolvedMeta0 (MetaHead m e) v -> catch @UnifyEx (checkMetaOccurs m *> S.Meta0 m ! psubst e) \_ -> psubst v
    TopDef0 i                    -> pure $ S.TopDef0 i
    DCon0 i                      -> pure $ S.DCon0 i
    App0 t u                     -> S.App0 ! psubst t ∙ psubst u
    Lam0 t                       -> S.Lam0 ! psubst t
    Decl0 t                      -> S.Decl0 ! psubst t
    Project0 t p                 -> S.Project0 ! psubst t ∙ pure p
    Splice t                     -> S.Splice ! psubst t
    Let0 t u                     -> S.Let0 ! psubst t ∙ psubst u


-- Nested solving
----------------------------------------------------------------------------------------------------

data RevSpine'
  = RSId'
  | RSApp' Val Name Icit ~VTy RevSpine'
  | RSProject' {-# nounpack #-} RecInfo Proj RevSpine'
  deriving Show

reverseSpine' :: (Spine -> Val) -> VTy -> Spine -> RevSpine'
reverseSpine' hd ~a sp = snd (go sp) where
  go :: Spine -> (VTy, RevSpine')
  go SId           = (a, RSId')
  go (SApp sp t i) = case go sp of
    (a, rsp) -> case appTy a t of
      (x, i, tty, a) -> (tty, RSApp' t x i tty rsp)
  go (SProject sp p) = case go sp of
    (a, rsp) -> case projTy (hd sp) a p of
      (inf, a) -> (a, RSProject' inf p rsp)

data Spine0 = S0Splice Spine | S0Id deriving (Show)

invertVal0 :: Lvl -> PartialSub -> Lvl -> Val0 -> Spine0 -> IO PartialSub
invertVal0 solvable psub param t rhsSp = case whnf0 t of
  LocalVar0 x -> do
    -- NOTE the "param == psub^.cod"
    -- This enforces that the rhsSp can only contain projections
    -- Otherwise we can't hope to solve, since the LHS is an object expression, so it can never be
    -- applied to invertible args. On the other hand, a spine that only contains projections can
    -- be trivially plugged into the solution.
    unless (solvable <= x && x < psub^.cod && param == psub^.cod) unifyError
    pure $! updatePSub0 psub x $ PV0Total $ case (rhsSp, psub^.domEnv) of
      (S0Id          , EBind0 _ v              ) -> v
      (S0Splice rhsSp, EBind _ (LocalDef y a v)) -> Splice $ Rigid (RHLocalVar y a) rhsSp
      _                                          -> impossible

  Splice (whnf -> Rigid rh@(RHLocalVar x a) sp) -> do
    case rhsSp of S0Id -> pure (); _ -> impossible
    unless (solvable <= x && x < psub^.cod) unifyError
    let rsp = reverseSpine' (Rigid rh) a sp
    pv <- solveNestedSp (psub^.domEnv) (psub^.cod) psub rsp SId
    pure $! updatePSub psub x pv

  _  -> unifyError

-- TODO: should return an extra isLinear
invertVal :: Lvl -> PartialSub -> Lvl -> Val -> Spine -> IO PartialSub
invertVal solvable psub param t rhsSp = case setLvl (psub^.cod) $ whnf t of

  Lam t -> do
    let var = LocalVar param (t^.ty)
    invertVal solvable psub (param + 1) (t ∙ var)
              (SApp rhsSp var (t^.icit))

  Quote t -> do
    invertVal0 solvable psub param t (S0Splice rhsSp)

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
    unless (solvable <= x && x < psub^.cod) unifyError
    let rsp = reverseSpine' (Rigid rh) a sp
    updatePSub psub x ! solveNestedSp (psub^.domEnv) (psub^.cod) psub rsp rhsSp

  _ -> unifyError

makeMCl :: Env -> Tm -> MultiClosure Val
makeMCl rootEnv t = MCl \args -> evalIn (foldl' EDef rootEnv args) t

solveNestedSp :: Env -> Lvl -> PartialSub -> RevSpine' -> Spine -> IO PartialVal
solveNestedSp rootEnv solvable psub rsp rhsSp = case rsp of

  RSId' -> do
    let hd = case rootEnv of
          EBind _ (LocalVar x a) -> S.LocalVar (lvlToIx (psub^.dom) x)
          _                      -> impossible
    body <- psubstIn psub rhsSp hd
    pure $! PVTotal $ makeMCl rootEnv body

  RSApp' u x i a rsp -> do
    a <- psubstIn psub a
    let ~va = evalIn (psub^.domEnv) a
    let d = psub^.dom
    let var = LocalVar d va
    psub <- invertVal solvable (psub & domEnv %~ (`EBind` var) & dom +~ 1) (psub^.cod) u SId
    pv <- solveNestedSp rootEnv solvable psub rsp rhsSp
    pure $! PVLam x i (makeMCl rootEnv a) pv

  RSProject' inf p rsp -> do
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

    pure $! PVRec inf $ mkFields (inf^.fields) (p^.index)


-- Top solving
----------------------------------------------------------------------------------------------------

-- | "Reverse environment" annotated with everything that we need to invert the Env.
data RevEnv
  = RENil
  | REDef   Name Tm  ~Val  Ty ~VTy RevEnv -- dom Tm, cod Val,  dom Ty, cod VTy
  | REBind  Name     ~Val  Ty ~VTy RevEnv --         cod Val,  dom Ty, cod VTy
  | REBind0 Name     ~Val0 Ty ~VTy RevEnv --         cod Val0, dom Ty, cod VTy

reverseEnv :: S.Locals -> Env -> RevEnv
reverseEnv ls e = go ls e RENil where
  go :: S.Locals -> Env -> RevEnv -> RevEnv
  go ls e acc = case (ls, e) of
    (S.LNil         , ENil      ) -> acc
    (S.LDef ls x t a, EDef e v  ) -> go ls e (REDef   x t v a (evalIn e a) acc)
    (S.LBind ls x a , EBind e v ) -> go ls e (REBind  x v a   (evalIn e a) acc)
    (S.LBind0 ls x a, EBind0 e v) -> go ls e (REBind0 x v a   (evalIn e a) acc)
    _                             -> impossible

-- We pass if the psub is linear, i.e. doesn't contain any Top.
solveTopMetaSub :: PartialSub -> Bool -> RevEnv -> RevSpine' -> Val -> IO S.Tm
solveTopMetaSub psub psubIsLinear renv rsp rhs = case renv of
  RENil -> solveTopSpine psub rsp rhs

  -- checks: 1) arg is invertible 2) if psubst is nonlinear, problem-scope *def* is psubst-able
  --         if either fails, we proceed without extending the psub
  REDef x t codvt a _ renv -> do
    let domVar = LocalDef (psub^.dom) (evalIn (psub^.domEnv) a) (evalIn (psub^.domEnv) t)
    let psub'  = psub & dom +~ 1 & domEnv %~ (`EDef` domVar)

    -- It only makes sense to map local defs to local defs. We don't need to worry about beta-eta
    -- stability, because local def inversion is purely an optimization and it's transparent to
    -- conversion.
    case whnf codvt of
      LocalDef x _ _ -> do
        psub' <- handle @UnifyEx (\_ -> pure psub') do
          unless psubIsLinear (() <$ psubstIn psub codvt)
          pure $! updatePSub psub' x $ PVTotal $ MCl \_ -> domVar
        solveTopMetaSub psub' psubIsLinear renv rsp rhs
      _ -> do
        solveTopMetaSub psub' psubIsLinear renv rsp rhs

  -- checks: 1) arg is invertible 2) if psubst is nonlinear, problem-scope binder *type* is psubst-able
  --         we block/fail if either fails
  ----------------------------------------------------------------------------------------------------

  REBind x codv a codva renv -> do
    let domVar = LocalVar (psub^.dom) (evalIn (psub^.domEnv) a)
    let psub' = psub & dom +~ 1 & domEnv %~ (`EDef` domVar)
    psub' <- invertVal 0 psub' (psub^.cod) codv SId
    unless psubIsLinear (() <$ psubstIn psub codva)
    solveTopMetaSub psub' psubIsLinear renv rsp rhs

  REBind0 x codv a codva renv -> do
    let domVar = LocalVar (psub^.dom) (evalIn (psub^.domEnv) a)
    let psub' = psub & dom +~ 1 & domEnv %~ (`EDef` domVar)
    psub' <- invertVal0 0 psub' (psub^.cod) codv S0Id
    unless psubIsLinear (() <$ psubstIn psub codva)
    solveTopMetaSub psub' psubIsLinear renv rsp rhs

solveTopSpine :: PartialSub -> RevSpine' -> Val -> IO S.Tm
solveTopSpine psub rsp rhs = case rsp of

  -- we don't need to check for invalid result type, because
  -- we already checked the types of all in-scope vars
  RSId' -> do
    psubstIn psub rhs

  RSApp' codv x i codva rsp -> do
    a <- psubstIn psub codva
    let domVar = LocalVar (psub^.dom) (evalIn (psub^.domEnv) a)
    let psub' = psub & dom +~ 1 & domEnv %~ (`EDef` domVar)
    psub' <- invertVal 0 psub' (psub^.cod) codv SId
    S.Lam . BindI x i a ! solveTopSpine psub' rsp rhs

  -- here I have to create fresh metas, so I need S.Locals
  -- I also need the type and value of the lhs "so far"
  RSProject' inf p rsp -> do
    _



-- data RevSpine'
--   = RSId'
--   | RSApp' Val Name Icit ~VTy RevSpine'
--   | RSProject' {-# nounpack #-} RecInfo Proj RevSpine'
--   deriving Show








----------------------------------------------------------------------------------------------------
