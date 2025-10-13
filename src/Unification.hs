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

--------------------------------------------------------------------------------
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

--------------------------------------------------------------------------------

freshMeta :: LocalsArg => Ty -> IO Tm
freshMeta a = C.Meta ! ES.newMeta a ∙ pure C.MSId

data UnifyEx = UETodo deriving Show
instance Exception UnifyEx

unifyError :: Dbg => IO a
unifyError = throwIO UETodo



-- Partial values
--------------------------------------------------------------------------------

-- | These closures abstract over all enclosing lambda binders in a PartialValue.
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

data PartialVal
  = PVTop
  | PVBot
  | PVVal PClosure
  | PVLam PClosure Name Icit PartialVal
  | PVRec {-# nounpack #-} RecInfo PartialRecFields
  deriving Show

data Path
  = PNil
  | PApp PClosure Name Icit Path
  | PProj {-# nounpack #-} RecInfo Proj Path
  deriving Show

data PartialSub = PSub {
    partialSubOccurs       :: Maybe MetaVar        -- ^ Optional meta occurs check
  , partialSubAllowPruning :: Bool                 -- ^ Can we prune metas during partial substitution
  , partialSubDomEnv       :: Env                  -- ^ Identity environment for the domain
  , partialSubDom          :: Lvl                  -- ^ Domain (size of the map)
  , partialSubCod          :: Lvl                  -- ^ Codomain (next fresh Lvl)
  , partialSubSub          :: IntMap PartialVal    -- ^ Total map from codomain vars to partial values
  }
makeFields ''PartialSub

type PSubArg = (?psub :: PartialSub)

setPSub :: PartialSub -> (PSubArg => a) -> a
setPSub s act = let ?psub = s in act

extendPVal :: Path -> PClosure -> PartialVal -> PartialVal
extendPVal path def pv = go path pv where

  -- -- create record fields of size numFields, where we insert a path at index "i"
  -- -- and we have PVBot everywhere else
  -- mkRec :: Ix -> Lvl -> Path -> PartialRecFieldsVal
  -- mkRec i numFields path = go' (ixToLvl numFields i) numFields Nil where
  --   go'  0 numFields acc = go'' (numFields - 1) (Snoc acc (go path PVBot))
  --   go'  i numFields acc = go'  (i - 1) (numFields - 1) (Snoc acc PVBot)
  --   go'' 0           acc = acc
  --   go'' i           acc = go'' (i - 1) (Snoc acc PVBot)

  go :: Path -> PartialVal -> PartialVal
  go path pv = case (path, pv) of
    (PNil           , PVBot         ) -> PVVal def
    (PApp _ _ _ path, PVLam a x i pv) -> PVLam a x i (go path pv)
    (PProj i p path , PVRec _ pvs   ) -> PVRec i uf
    (PApp a x i path, PVBot         ) -> PVLam a x i (go path PVBot)
    (PProj i p path , PVBot         ) -> PVRec i uf
    _                                 -> PVTop

lift :: PartialSub -> PartialSub
lift (PSub occ pr idenv dom cod sub) =
  let var = LocalVar dom in
  PSub occ pr (EDef idenv var) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PVVal $ PCl \_ -> var) sub

update :: Lvl -> Path -> PClosure -> PartialSub -> PartialSub
update x path def psub =
  let ~newpv = extendPVal path def PVBot in
  psub & sub %~ IM.insertWith (\_ -> extendPVal path def) (fromIntegral x) newpv

-- Partial substitution
--------------------------------------------------------------------------------

class PSubst a b | a -> b where
  psubst :: PSubArg => a -> b

instance PSubst Lvl PartialVal where
  psubst x = (?psub^.sub) IM.! fromIntegral x

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

instance PSubst Val (IO Tm) where
  psubst = \case
    Rigid h sp -> case h of
      RHLocalVar x -> applyPVal (psubst x) (reverseSpine sp) []
      RHPrim i     -> psubst sp (C.Prim i)
      RHDCon i     -> psubst sp (C.DCon i)
      RHTCon i     -> psubst sp (C.TCon i)
      RHRecTy i    -> psubst sp (C.RecTy i)
      RHRec i      -> psubst sp (C.Rec i)
    Flex m sp -> uf

-- Readback
--------------------------------------------------------------------------------

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














--------------------------------------------------------------------------------
