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

-}

----------------------------------------------------------------------------------------------------

freshMeta :: LocalsArg => Ty -> IO Tm
freshMeta a = S.Meta ! ES.newMeta a ∙ pure S.MSId

data UnifyEx = UETodo deriving Show
instance Exception UnifyEx

unifyError :: Dbg => IO a
unifyError = throwIO UETodo


-- Partial values
----------------------------------------------------------------------------------------------------

-- | Closures abstract over all enclosing lambda binders in a PartialVal. PartialVal can be viewed
--   as a partial *term* wrapped in an explicit weakening. The weakenings are pushed down to the
--   types & terms in the inside and represented as closures.
newtype PClosure = PCl ([Val] -> Val)

instance Show PClosure where showsPrec _ _ acc = "<closure>" ++ acc

instance Apply PClosure [Val] Val where
  (∙∘) (PCl f) (vs,_) = f vs; {-# inline (∙∘) #-}

data PartialRecFields
  = PRFNil
  | PRFSnoc PartialRecFields PartialVal Icit
  deriving Show

instance ElemAt PartialRecFields Ix PartialVal where
  elemAt pvs i = case (pvs, i) of
    (PRFSnoc _ v _  , 0) -> v
    (PRFSnoc pvs _ _, i) -> elemAt pvs (i - 1)
    _                    -> impossible

instance UpdateAt PartialRecFields Ix PartialVal where
  {-# inline updateAt #-}
  updateAt pvs ix f = go pvs ix where
    go (PRFSnoc pvs v i) 0  = PRFSnoc pvs (f v) i
    go (PRFSnoc pvs v i) ix = PRFSnoc (go pvs (ix - 1)) v i
    go _                 _  = impossible

data PartialVal
  = PVTop
  | PVBot
  | PVVal0 Lvl
  | PVVal PClosure
  | PVLam PClosure Name Icit PartialVal
  | PVRec {-# nounpack #-} RecInfo PartialRecFields
  deriving Show

data Path
  = PNil
  | PApp PClosure Name Icit Path
  | PSplice Path
  | PProj {-# nounpack #-} RecInfo Proj Path
  deriving Show

data PartialSub = PSub {
    partialSubOccurs       :: Maybe MetaVar     -- ^ Optional meta occurs check
  , partialSubAllowPruning :: Bool              -- ^ Can we prune metas
  , partialSubDomEnv       :: Env               -- ^ Identity environment for the domain
  , partialSubDom          :: Lvl               -- ^ Domain (size of the map)
  , partialSubCod          :: Lvl               -- ^ Codomain (next fresh Lvl)
  , partialSubSub          :: IntMap PartialVal -- ^ Total map from codomain vars to partial values
  }
makeFields ''PartialSub

type PSubArg = (?psub :: PartialSub)

setPSub :: PartialSub -> (PSubArg => a) -> a
setPSub s act = let ?psub = s in act

extendPVal :: Path -> PClosure -> PartialVal -> PartialVal
extendPVal path def pv = go path pv where

  botFields :: FieldInfo -> PartialRecFields
  botFields = \case
    FINil           -> PRFNil
    FISnoc fs x i a -> PRFSnoc (botFields fs) PVBot i

  mkFields :: FieldInfo -> Ix -> Path -> PartialRecFields
  mkFields fs ix path = case (fs, ix) of
    (FISnoc fs x i a, 0 ) -> PRFSnoc (botFields fs) (go path PVBot) i
    (FISnoc fs x i a, ix) -> PRFSnoc (mkFields fs (ix - 1) path) PVBot i
    _                     -> impossible

  go :: Path -> PartialVal -> PartialVal
  go path pv = case (path, pv) of
    (PNil           , PVBot         ) -> PVVal def
    (PApp _ _ _ path, PVLam a x i pv) -> PVLam a x i (go path pv)
    (PProj i p path , PVRec _ pvs   ) -> PVRec i (updateAt pvs (p^.index) (go path))
    (PApp a x i path, PVBot         ) -> PVLam a x i (go path PVBot)
    (PProj i p path , PVBot         ) -> PVRec i (mkFields (i^.fields) (p^.index) path)
    _                                 -> PVTop

lift :: VTy -> PartialSub -> PartialSub
lift ~a (PSub occ pr idenv dom cod sub) =
  let var = LocalVar dom a in
  PSub occ pr (EDef idenv var) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PVVal $ PCl \_ -> var) sub

lift0 :: PartialSub -> PartialSub
lift0 (PSub occ pr idenv dom cod sub) =
  PSub occ pr (EDef0 idenv dom) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PVVal0 dom) sub

updatePSub :: Lvl -> Path -> PClosure -> PartialSub -> PartialSub
updatePSub x path def psub =
  let ~newpv   = extendPVal path def PVBot
      ext _ pv = extendPVal path def pv in
  psub & sub %~ IM.insertWith ext (fromIntegral x) newpv


-- Partial substitution
----------------------------------------------------------------------------------------------------

class PSubst a b | a -> b where
  psubst :: PSubArg => a -> b

instance PSubst Lvl PartialVal where
  psubst x = (?psub^.sub) IM.! fromIntegral x

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
      EDef0 e x -> S.TEDef0 ! go e ∙ setLvl (?psub^.dom) (readbPVal0 (psubst x))

applyPVal :: PSubArg => PartialVal -> RevSpine -> [Val] -> IO Tm
applyPVal pv sp args = case (pv, sp) of
  (PVLam a _ _ pv, RSApp t i sp  ) -> do t <- psubst t
                                         applyPVal pv sp (evalIn (?psub^.domEnv) t : args)
  (PVRec i pvs   , RSProject p sp) -> applyPVal (elemAt pvs (p^.index)) sp args
  (PVVal v       , sp            ) -> psubst sp (readBackNoUnfold (?psub^.dom) (v ∙ args))
  (pv            , RSId          ) -> setLvl (?psub^.dom) $ setUnfold UnfoldNone $ readbPVal pv args
  _                                -> unifyError

approxOccursInMeta :: MetaVar -> MetaVar -> IO ()
approxOccursInMeta occ m = error "TODO"

checkMetaOccurs :: PSubArg => MetaVar -> IO ()
checkMetaOccurs m = case ?psub^.occurs of
  Just m' -> when (m == m') unifyError
  _       -> pure ()

instance PSubst ClosureI (IO (BindI Tm)) where
  psubst (ClI a x i t) = _
    -- BindI ! (psubst a) ∙ pure a ∙
    -- setPSub (lift ?psub) $ BindI x i ! psubst (t (LocalVar (?psub^.cod)))

instance PSubst Val (IO Tm) where
  psubst v = case force v of
    Rigid h sp -> case h of
      RHLocalVar x _ -> applyPVal (psubst x) (reverseSpine sp) []
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
            UHMeta (MetaHead m e) -> do {checkMetaOccurs m; S.Meta m ! psubst e}
            UHTopDef i            -> pure $ S.TopDef i
            UHLocalDef x          -> applyPVal (psubst x) (reverseSpine sp) []
      catch @UnifyEx (psubst sp =<< goHead) \_ -> psubst v

    Pi b    -> S.Pi ! psubst b
    Lam t   -> S.Lam ! psubst t
    Quote t -> S.Quote ! psubst t

instance PSubst Closure0 (IO (Bind Tm0)) where
  psubst (Cl0 x a f) = _
    -- setPSub (lift0 ?psub) $ Bind x ! psubst (f (?psub^.cod))

instance PSubst Val0 (IO Tm0) where
  psubst t = case force0 t of
    LocalVar0 x                  -> setLvl (?psub^.dom) $ setUnfold UnfoldNone $
                                           (S.LocalVar0 ! readbPVal0 (psubst x))
    Meta0 (MetaHead m e)         -> do {checkMetaOccurs m; S.Meta0 m ! psubst e}
    SolvedMeta0 (MetaHead m e) v -> catch @UnifyEx (do {checkMetaOccurs m; S.Meta0 m ! psubst e}) \_ -> psubst v
    TopDef0 i                    -> pure $ S.TopDef0 i
    DCon0 i                      -> pure $ S.DCon0 i
    App0 t u                     -> S.App0 ! psubst t ∙ psubst u
    Lam0 t                       -> S.Lam0 ! psubst t
    Decl0 t                      -> S.Decl0 ! psubst t
    Project0 t p                 -> S.Project0 ! psubst t ∙ pure p
    Splice t                     -> S.Splice ! psubst t

instance ReadBack PartialRecFields ([Val] -> Tm -> IO Tm) where
  readb pvs args hd = case pvs of
    PRFNil           -> pure hd
    PRFSnoc pvs pv i -> S.App ! readb pvs args hd ∙ readbPVal pv args ∙ pure i

readbPVal :: LvlArg => UnfoldArg => PartialVal -> [Val] -> IO Tm
readbPVal pv args = case pv of
  PVTop          -> unifyError
  PVBot          -> unifyError
  PVVal v        -> pure $! readb (v ∙ args)
  PVVal0 x       -> impossible
  PVLam a x i pv -> _
                    -- let a' = readb (a ∙ args) in
                    -- fresh \v -> S.Lam a' . BindI x i a' ! readbPVal pv (v:args)
  PVRec i pvs    -> readb pvs args (S.Rec i)

readbPVal0 :: LvlArg => PartialVal -> IO Ix
readbPVal0 pv = case pv of
  PVTop    -> unifyError
  PVBot    -> unifyError
  PVVal0 x -> pure $! lvlToIx ?lvl x
  PVVal{};PVLam{};PVRec{} -> impossible


-- Inversion
----------------------------------------------------------------------------------------------------

invertVal0 :: Lvl -> PartialSub -> Lvl -> Val0 -> Path -> IO PartialSub
invertVal0 solvable psub param t path = case setLvl param $ whnf0 t of
  LocalVar0 x -> uf

invertVal :: Lvl -> PartialSub -> Lvl -> Val -> Path -> IO PartialSub
invertVal solvable psub param t path = case setLvl param $ whmnf t of

  Lam t -> do
    -- a <- setPSub psub $ psubst (t^.ty)
    -- let ~va = evalIn (psub^.domEnv) a
    -- let ~qa = setLvl (psub^.dom) readb
    let var = LocalVar param (t^.ty)
    let ?lvl = param + 1
    invertVal solvable psub ?lvl (t ∙ var) (PApp _ (t^.name) (t^.icit) path)

  Quote t -> do
    invertVal0 solvable psub param t (PSplice path)

  Rigid (RHLocalVar x a) sp -> do
    unless (solvable <= x && x < psub^.cod) unifyError

    let psub' = PSub Nothing False (psub^.domEnv) (psub^.dom) param (psub^.sub)
    (path, sol) <- solveNestedSp (psub^.cod) psub' uf (reverseSpine sp) uf
    uf

  Rigid (RHRec i) sp -> do
    uf

  Unfold (UHLocalDef x) sp t -> do
    uf

  Unfold _ _ t ->
    invertVal solvable psub param t path

  _ -> unifyError

solveNestedSp :: Lvl -> PartialSub -> VTy -> RevSpine -> (Lvl, Path) -> IO (Path, PClosure)
solveNestedSp solvable psub a sp (!rhsVar, !rhsPath) = do
  uf


-- solveTop :: PartialSub
-- solveTopSp :: PartialSub ->




----------------------------------------------------------------------------------------------------
