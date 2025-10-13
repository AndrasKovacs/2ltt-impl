{-# options_ghc -Wno-unused-imports #-}

module Unification where

import Common
import Core (Ty, Tm, Locals, LocalsArg, RecInfo)
import qualified Core as C
import Value
import qualified Elaboration.State as ES
import Evaluation
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

----------------------------------------------------------------------------------------------------

{-

Speculations

  1. Libal-Miller unification: https://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/fcu-final.pdf

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
-}

----------------------------------------------------------------------------------------------------

freshMeta :: LocalsArg => Ty -> IO Tm
freshMeta a = C.Meta ! ES.newMeta a ∙ pure C.MSId

data UnifyEx = UETodo deriving Show
instance Exception UnifyEx

unifyError :: Dbg => IO a
unifyError = throwIO UETodo



-- Partial values
----------------------------------------------------------------------------------------------------

-- | These closures abstract over all enclosing lambda binders in a PartialVal.
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
  | PVVal PClosure
  | PVLam PClosure Name Icit PartialVal
  | PVRec {-# nounpack #-} RecInfo PartialRecFields
  deriving Show

data PartialVal0
  = PV0Val Lvl
  | PV0Top
  | PV0Bot
  deriving Show

data PSEntry
  = PSVal PartialVal
  | PSVal0 PartialVal0
  deriving Show

data Path
  = PNil
  | PApp PClosure Name Icit Path
  | PProj {-# nounpack #-} RecInfo Proj Path
  deriving Show

data PartialSub = PSub {
    partialSubOccurs       :: Maybe MetaVar   -- ^ Optional meta occurs check
  , partialSubAllowPruning :: Bool            -- ^ Can we prune metas
  , partialSubDomEnv       :: Env             -- ^ Identity environment for the domain
  , partialSubDom          :: Lvl             -- ^ Domain (size of the map)
  , partialSubCod          :: Lvl             -- ^ Codomain (next fresh Lvl)
  , partialSubSub          :: IntMap PSEntry  -- ^ Total map from codomain vars to partial values
  }
makeFields ''PartialSub

type PSubArg = (?psub :: PartialSub)

setPSub :: PartialSub -> (PSubArg => a) -> a
setPSub s act = let ?psub = s in act

extendPVal :: Path -> PClosure -> PartialVal -> PartialVal
extendPVal path def pv = go path pv where

  botFields :: C.FieldInfo -> PartialRecFields
  botFields = \case
    C.FINil           -> PRFNil
    C.FISnoc fs x i a -> PRFSnoc (botFields fs) PVBot i

  mkFields :: C.FieldInfo -> Ix -> Path -> PartialRecFields
  mkFields fs ix path = case (fs, ix) of
    (C.FISnoc fs x i a, 0 ) -> PRFSnoc (botFields fs) (go path PVBot) i
    (C.FISnoc fs x i a, ix) -> PRFSnoc (mkFields fs (ix - 1) path) PVBot i
    _                       -> impossible

  go :: Path -> PartialVal -> PartialVal
  go path pv = case (path, pv) of
    (PNil           , PVBot         ) -> PVVal def
    (PApp _ _ _ path, PVLam a x i pv) -> PVLam a x i (go path pv)
    (PProj i p path , PVRec _ pvs   ) -> PVRec i (updateAt pvs (p^.index) (go path))
    (PApp a x i path, PVBot         ) -> PVLam a x i (go path PVBot)
    (PProj i p path , PVBot         ) -> PVRec i (mkFields (i^.C.fields) (p^.index) path)
    _                                 -> PVTop

lift :: PartialSub -> PartialSub
lift (PSub occ pr idenv dom cod sub) =
  let var = LocalVar dom in
  PSub occ pr (EDef idenv var) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PSVal $ PVVal $ PCl \_ -> var) sub

lift0 :: PartialSub -> PartialSub
lift0 (PSub occ pr idenv dom cod sub) =
  PSub occ pr (EDef0 idenv dom) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PSVal0 $ PV0Val dom) sub

update :: Lvl -> Path -> PClosure -> PartialSub -> PartialSub
update x path def psub =
  let ~newpv           = PSVal (extendPVal path def PVBot)
      ext _ (PSVal pv) = PSVal (extendPVal path def pv)
      ext _ _          = impossible in
  psub & sub %~ IM.insertWith ext (fromIntegral x) newpv


-- Partial substitution
----------------------------------------------------------------------------------------------------

class PSubst a b | a -> b where
  psubst :: PSubArg => a -> b

-- instance PSubst Lvl PartialVal where
--   psubst x = case (?psub^.sub) IM.! fromIntegral x of
--     PSVal pv -> pv
--     _        -> impossible

psubstLvl :: PSubArg => Lvl -> PartialVal
psubstLvl x = case (?psub^.sub) IM.! fromIntegral x of
  PSVal pv -> pv
  _        -> impossible

psubstLvl0 :: PSubArg => Lvl -> PartialVal0
psubstLvl0 x = case (?psub^.sub) IM.! fromIntegral x of
  PSVal0 pv -> pv
  _         -> impossible

instance PSubst Spine (Tm -> IO Tm) where
  psubst t hd = case t of
    SId          -> pure hd
    SApp t u i   -> C.App ! psubst t hd ∙ psubst u ∙ pure i
    SProject t p -> C.Project ! psubst t hd ∙ pure p

instance PSubst RevSpine (Tm -> IO Tm) where
  psubst sp acc = case sp of
    RSId           -> pure acc
    RSApp t i sp   -> do t <- psubst t; psubst sp (C.App acc t i)
    RSProject p sp -> psubst sp (C.Project acc p)

applyPVal :: PSubArg => PartialVal -> RevSpine -> [Val] -> IO Tm
applyPVal pv sp args = case (pv, sp) of
  (PVLam a _ _ pv, RSApp t i sp  ) -> do t <- psubst t
                                         applyPVal pv sp (evalIn (?psub^.domEnv) t : args)
  (PVRec i pvs   , RSProject p sp) -> applyPVal (elemAt pvs (p^.index)) sp args
  (PVVal v       , sp            ) -> psubst sp (readBack (?psub^.dom) UnfoldNone (v ∙ args))
  (pv            , RSId          ) -> readBack (?psub^.dom) UnfoldNone pv args
  _                                -> unifyError

-- TODO: detect identity substitution
instance PSubst Env (IO C.MetaSub) where
  psubst e = C.MSSub ! go e where
    go :: Env -> IO C.TmEnv
    go = \case
      ENil      -> pure C.TENil
      ELet e v  -> C.TELet  ! go e ∙ psubst v
      EDef e v  -> C.TEDef  ! go e ∙ psubst v
      EDef0 e x -> C.TEDef0 ! go e ∙ readBack (?psub^.dom) UnfoldNone (psubstLvl0 x)

instance PSubst MetaHead (IO Tm) where
  psubst (MetaHead m e) = do
    case ?psub^.occurs of Just m' -> when (m == m') unifyError
                          _       -> pure ()
    C.Meta m ! psubst e

instance PSubst Val (IO Tm) where
  psubst v = case force v of
    Rigid h sp -> case h of
      RHLocalVar x -> applyPVal (psubstLvl x) (reverseSpine sp) []
      RHPrim i     -> psubst sp (C.Prim i)
      RHDCon i     -> psubst sp (C.DCon i)
      RHTCon i     -> psubst sp (C.TCon i)
      RHRecTy i    -> psubst sp (C.RecTy i)
      RHRec i      -> psubst sp (C.Rec i)

    -- TODO: pruning
    Flex m sp -> do hd <- psubst m; psubst sp hd

-- Readback
----------------------------------------------------------------------------------------------------

instance ReadBack PartialVal0 (IO Ix) where
  readb = \case
    PV0Val x -> pure $! readb x
    PV0Top   -> unifyError
    PV0Bot   -> unifyError

instance ReadBack PartialRecFields ([Val] -> Tm -> IO Tm) where
  readb pvs args hd = case pvs of
    PRFNil           -> pure hd
    PRFSnoc pvs pv i -> C.App ! readb pvs args hd ∙ readb pv args ∙ pure i

instance ReadBack PartialVal ([Val] -> IO Tm) where
  readb pv args = case pv of
    PVTop          -> unifyError
    PVBot          -> unifyError
    PVVal v        -> pure $! readb (v ∙ args)
    PVLam a x i pv -> let a' = readb (a ∙ args) in
                      fresh \v -> C.Lam a' . BindI x i ! readb pv (v:args)
    PVRec i pvs    -> readb pvs args (C.Rec i)














----------------------------------------------------------------------------------------------------
