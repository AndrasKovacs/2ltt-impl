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
{- quick list of todo fancy features
  - nested pattern unification
  - weak Libal-Miller unification
  - partial substitution returning partial results
  - eliminator inversions
  - non-escaping meta optimization
  - local let-def preservation
  - observational def-eq coercions
-}

{-

Libal-Miller unification: https://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/fcu-final.pdf

    - It's very hard to do in a full & stable way.
      Checking subterms is best done with hash-consing and eta-short normalization.
      Then, we have to somehow do tree matching during psubst. For that, starting
      with eta-short normal hash-consing on the rhs would also be an option.
      However, eta-short normal hash-consing is extremely expensive and doesn't
      support incremental unfolding.

    - We may try a simpler limited version:
        - Instead of checking subterm relations, we require bound variables to be *disjoint* in
          spine terms. If we invert some term, we only attach path information to the
          preorder-first bound var ("anchor"), and mark all other bound vars in the term as
          illegal. During psubst, if we hit an anchor var, we throw the anchor path as an exception
          and bubble up to the root of the path. At that point, we can do a conversion check to see
          if the inversion rule fires.
        - This is also rather complex, and I don't see an obvious way to do it in a nested way.
          Doing it in a nested way would be important, because nested pattern unification handles
          eta-expansions, and if I do Libal-Miller separately in the top spine, I have to do
          eta-reductions.

    - We might just hardwire simple cases like Lift, ElVal and ElComp. And see in practice which
      Libal-Miller problem pop up, to assess the practical benefit.

Optimization for non-escaping metas

  Most metas don't escape the scope of their creation, so we want to optimize for that case.
  Concretely, the cost of operations on non-escaping metas should not depend on the size of the
  local scope.

    - fresh meta creation is already O(1) in local scope
    - TODO metasub inversion should be O(1). We need to represent weakened identity env-s in values,
      shortcut inversion for that case.
    - TODO pruning should be O(1). Need to shortcut pruning subst creation if one meta scope is contained
      in the other one.

Inverting local defs

  Mapping to a defined domain var is an merely an *optimization* whose goal is preserving unfoldings,
  it can't fail in a hard way.

    - If inversion fails, we can simply continue; the only effect is that the domain definition will
      be unused in the solution (but may be still used in the solution type).
      When psubst-ing the solution candidate, we simply unfold those local defs which are not mapped
      in the psub.
    - We can invert codomain definitions opportunistically

  Example: "a" and "x" are both defined.

       a
     α x =? rhs
     x ↦ a
     α := λ a. rhs[x↦a]

     We simply rename local definitions.

  Example: "a", "x", "y" are defined

       a
    α (x, y) =? rhs
    x ↦ a.1
    y ↦ a.2
    α := λ a. rhs[x↦a.1, y↦a.2]

  Codomain local defs behave like bound vars for the purpose of inversion
  When inversion fails for a defvar-headed spine, we unfold and retry.

  We need two different modes for inversion
    - mapping to defvar: don't whnf, retry localdef inversion with unfolding
    - mapping to bvar: always whnf


Postponing

  - TODO
  - Need to track strong rigid/rigid/flex occurrences in errors
  - Need placeholders metas
  - NEW: fine-grain blocking: psubst failure gets *locally* replaced with placeholder metas
    - We bubble up to the outermost rigid or flex context
    - At *that* point we make a postponed problem and return a placeholder meta
    - Makes more progress than Agda!

  - Do we want to block on a single meta or more?
     In psubst, we might fail under multiple metas

  - JUST LEARNED ABOUT AGDA'S ANTI-UNIFICATION
    - Can we *just* keep unifying telescopes in a syntax-directed setting, by doing
      absolutely nothing???
    - Is this "typing modulo"?
    - IDEA: we relax the homogenity of unification. Since we only need homogenity for syntax-directed
      eta rules, we only need that:
        - when one side is Π, the other one is Π too with the same Icit-ness
        - when one side is a record, the other one is a record with the same arity

    - Does it even work?

         f : (b : Bool) → (if b then (Bool → Bool) else Bool) → C

         f true (λ x. x) =? f (α true) y

         postpone "true =? α true"

         (λ x. x : Bool → Bool) =? (y : if α true then (Bool → Bool) else Bool)

         No, it doesn't work!
         In Agda, anti-unification works because eta-expansion is type-directed,
         and it can only happen if both sides have Π/Σ type

    - Lesson: heterogeneous unification can make progress, but it requires computing types

    - Can we use some kind of computing meta-transport, without OTT or cubical, to get
      progress under postponed equality?

       f : (x : A) → B x → C
       f t u =? f t' u'

       cast (B t) (B t') u =? u'

       fancy "cast" operation which becomes definitional identity if t ≡ t'

      Basically: Yes, and it's probably a better solution than heterogeneous
      unification

Observational conversion
  TODO

Partial substitution returning partial result:
  TODO
  - if we have a soft failure of psubst, we bubble up to the enclosing strong
    rigid context and plug in a placeholder meta, and succeed.

Pruning
  TODO



IMPL:
  - copy from my sett version
  - except that partial values have transparent multi-closure defn
  - I don't have to check rhs type psubst in nested spine solution
     - because non-linear args always blow up there and we psubst
       every solution lambda binder anyway
  - But I do have to check it in top spine solution
     (if there's any non-linearity in the psubst)

-}

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

-- unlift :: PartialSub -> PartialSub
-- unlift (PSub occ pr idenv dom cod sub) =
--   PSub occ pr (envTail idenv) (dom - 1) (cod - 1) (IM.delete (fromIntegral dom) sub)

lift0 :: PartialSub -> PartialSub
lift0 (PSub occ pr idenv dom cod sub) =
  let var = LocalVar0 dom in
  PSub occ pr (EDef0 idenv var) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PSEVal0 (PV0Total var)) sub

updatePSub :: PartialSub -> Lvl -> PartialVal -> PartialSub
updatePSub psub x pv =
  psub & sub %~ IM.insertWith (<>) (fromIntegral x) (PSEVal pv)

updatePSub0 :: PartialSub -> Lvl -> PartialVal0 -> PartialSub
updatePSub0 psub x pv =
  psub & sub %~ IM.insertWith (<>) (fromIntegral x) (PSEVal0 pv)

-- Partial substitution
----------------------------------------------------------------------------------------------------

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
      ENil      -> pure S.TENil
      ELet e v  -> S.TELet  ! go e ∙ psubst v
      EDef e v  -> S.TEDef  ! go e ∙ psubst v
      EDef0 e v -> S.TEDef0 ! go e ∙ psubst v

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
      RHLocalVar x _ -> applyPVal (psubstLvl x) (reverseSpine sp) []
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
            UHLocalDef x          -> applyPVal (psubstLvl x) (reverseSpine sp) []
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


-- Inversion
----------------------------------------------------------------------------------------------------

data Spine0 = S0Splice Spine | S0Id deriving Show

data Rhs sp = Rhs {rhsLvl :: Lvl, rhsTy :: ~VTy, rhs_ :: sp} deriving Show
makeFields ''Rhs

rhsSpine :: Lens (Rhs sp) (Rhs sp') sp sp'
rhsSpine f (Rhs x a sp) = Rhs x a <$> f sp

spine0 :: Rhs Spine0 -> Val0
spine0 (Rhs x a sp) = case sp of
  S0Id        -> LocalVar0 x
  S0Splice sp -> Splice $ Rigid (RHLocalVar x a) sp

invertVal0 :: Lvl -> PartialSub -> Lvl -> Val0 -> Rhs Spine0 -> IO PartialSub
invertVal0 solvable psub param t rhs = case whnf0 t of
  LocalVar0 x -> do
    unless (solvable <= x && x < psub^.cod) unifyError
    pure $! updatePSub0 psub x $ PV0Total $ spine0 rhs
  Splice (LocalVar x a) -> do
    unless (solvable <= x && x < psub^.cod) unifyError
    let v = Quote (spine0 rhs)
    pure $! updatePSub psub x $ PVTotal $ MCl \_ -> v
  _  -> unifyError

invertVal :: Lvl -> PartialSub -> Lvl -> Val -> Rhs Spine -> IO PartialSub
invertVal solvable psub param t rhs = case setLvl (psub^.cod) $ whmnf t of

  Lam t -> do
    let var = LocalVar param (t^.ty)
    invertVal solvable psub (param + 1) (t ∙ var)
              (rhs & rhsSpine %~ \sp -> SApp sp var (t^.icit))

  Quote t -> do
    invertVal0 solvable psub param t (rhs & rhsSpine %~ S0Splice)

  Rigid (RHRec i) sp -> do

    let go :: PartialSub -> FieldInfo -> Spine -> Ix -> IO PartialSub
        go psub fs sp ix = case (fs, sp) of
          (FINil, SId                  ) -> pure psub
          (FISnoc fs x i a, SApp sp t _) -> do
            psub <- go psub fs sp (ix + 1)
            invertVal solvable psub param t (rhs & rhsSpine %~ (`SProject` Proj ix x))
          _ -> impossible

    go psub (i^.fields) sp 0

  Rigid (RHLocalVar x a) sp -> do
    unless (solvable <= x && x < psub^.cod) unifyError
    updatePSub psub x ! solveNestedSp (psub^.domEnv) (psub^.cod) psub a (reverseSpine sp) rhs

  -- TODO: preserve local definitions (if we are mapping to a local definition!)
  Unfold _ _ t -> do
    invertVal solvable psub param t rhs

  _ -> unifyError

makeMCl :: Env -> Tm -> MultiClosure Val
makeMCl rootEnv t = MCl \args -> evalIn (foldl' EDef rootEnv args) t

solveNestedSp :: Env -> Lvl -> PartialSub -> VTy -> RevSpine -> Rhs Spine -> IO PartialVal
solveNestedSp rootEnv solvable psub a rsp rhs = case rsp of

  RSId -> do
    let hd = S.LocalVar (lvlToIx (psub^.dom) (rhs^.lvl))
    pv <- psubstIn psub (rhs^.rhsSpine) hd
    pure $! PVTotal $ makeMCl rootEnv pv

  sp -> case (whnf a, rsp) of
    (Pi b, RSApp u _ sp) -> do
      a <- psubstIn psub (b^.ty)
      let ~va = evalIn (psub^.domEnv) a
      let d = psub^.dom
      let v = LocalVar d va
      psub' <- invertVal solvable (psub & domEnv %~ (`EDef` v) & dom +~ 1)
                                  (psub^.cod) u (Rhs d va SId)
      pv <- solveNestedSp rootEnv solvable psub' (b ∙ v) sp rhs
      pure $! PVLam (b^.name) (b^.icit) (makeMCl rootEnv a) pv

    (Rigid (RHRecTy i) sp, RSProject p rsp) -> do
      pv <- solveNestedSp rootEnv solvable psub _ rsp rhs
      _


-- solveNestedSp :: Lvl -> PartialSub -> VTy -> RevSpine -> Lvl -> VTy -> Spine -> IO PartialVal
-- solveNestedSp solvable psub a sp rhsVar rhsVarTy rhsSp = case sp of

--   RSId -> do
--     let rhs = setLvl (psub^.dom) $ setUnfold UnfoldNone $ readb rhsSp (S.LocalVar (readb rhsVar))
--     pure $! PVTotal $! mkMCl psub rhsVar rhs

--   sp -> case (whnf a, sp) of
--     (Pi b, RSApp u _ t) -> do
--       a <- setPSub psub $ psubst (b^.ty)
--       psub <- invertVal solvable psub _ _ _ _
--       _

--       -- PVLam (b^.name) (b^.icit) (mkMCl psub rhsVar a) !


----------------------------------------------------------------------------------------------------
