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

  1. Libal-Miller unification:
    - Trying some kind of "rewrite rule" substitution is way too expensive
    - We should use that for every inverted term we can pick the inorder-first
      bound var as the "anchor". Somehow we want to remember a "hole" for the anchor,
      and everything in the hole context should be somehow conversion checked in
      the partial substitution.
    - Idea: for each anchor variable, we remember the path to the root of the
      enclosing term. When psubst hits an anchor variable, we throw the path as
      exception, then bubble up all the way to the root. At that point we can
      do a conversion check in the *codomain*, comparing the target codomain value
      to the Libal-Miller term. If the check succeeds, we return the corresponding domain
      variable.
      - Simpler version: only do Libal-Miller inversion in top-level solveSp
      - Full version: integrate Libal-Miller to nested unification everywhere

-}

--------------------------------------------------------------------------------

freshMeta :: LocalsArg => Ty -> IO Tm
freshMeta a = C.Meta ! ES.newMeta a ∙ pure C.MSId

--------------------------------------------------------------------------------

data UnifyEx = UETodo deriving Show
instance Exception UnifyEx

unifyError :: Dbg => IO a
unifyError = throwIO UETodo

--------------------------------------------------------------------------------

-- ^ These closures abstract over all enclosing lambda binders in a PartialValue.
newtype PClosure = PCl ([Val] -> Val)

instance Show PClosure where showsPrec _ _ acc = "<closure>" ++ acc

instance Apply PClosure [Val] Val where
  (∙∘) (PCl f) (vs,_) = f vs; {-# inline (∙∘) #-}

data PartialVal
  = PVTop
  | PVBot
  | PVVal PClosure
  | PVLam PClosure PartialVal
  | PVRec (SnocList PartialVal)
  deriving Show

data Path
  = PNil
  | PApp PClosure Icit Path
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

  mkRec :: Ix -> Lvl -> Path -> SnocList PartialVal
  mkRec i numFields path = go' (ixToLvl numFields i) numFields Nil where
    go'  0 numFields acc = go'' (numFields - 1) (Snoc acc (go path PVBot))
    go'  i numFields acc = go'  (i - 1) (numFields - 1) (Snoc acc PVBot)
    go'' 0           acc = acc
    go'' i           acc = go'' (i - 1) (Snoc acc PVBot)

  go :: Path -> PartialVal -> PartialVal
  go path pv = case (path, pv) of
    (PNil          , PVBot     ) -> PVVal def
    (PApp _ _ path , PVLam a pv) -> PVLam a (go path pv)
    (PProj i p path, PVRec pvs ) -> PVRec $ updateAt (p^.index) pvs $ go path
    (PApp a i path , PVBot     ) -> PVLam a (go path PVBot)
    (PProj i p path, PVBot     ) -> PVRec $ mkRec (p^.index) (i^.C.numFields) path
                                 -- ^ same as updateAt (p^.index) (replicate (i^.numFields) PVBot) (go path)
    _                            -> PVTop

lift :: PartialSub -> PartialSub
lift (PSub occ pr idenv dom cod sub) =
  let var = LocalVar dom in
  PSub occ pr (EDef idenv var) (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PVVal $ PCl \_ -> var) sub

update :: Lvl -> Path -> PClosure -> PartialSub -> PartialSub
update x path def psub =
  let ~newpv = extendPVal path def PVBot in
  psub & sub %~ IM.insertWith (\_ -> extendPVal path def) (fromIntegral x) newpv

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
  (PVLam a pv, RSApp t i sp  ) -> do t <- psubst t
                                     applyPVal pv sp (evalIn (?psub^.domEnv) t : args)
  (PVRec pvs , RSProject p sp) -> applyPVal (indexList pvs (p^.index)) sp args
  (PVVal v   , sp            ) -> psubst sp (readBack (?psub^.dom) UnfoldNone (v ∙ args))
  (pv        , RSId          ) -> readBack (?psub^.dom) UnfoldNone pv args
  _                            -> unifyError

instance ReadBack (List PartialVal) ([Val] -> Tm -> IO Tm) where
  readb pvs args hd = uf

instance ReadBack PartialVal ([Val] -> IO Tm) where
  readb pv args = case pv of
    PVTop      -> unifyError
    PVBot      -> unifyError
    PVVal v    -> pure $! readb (v ∙ args)
    PVLam a pv -> C.Lam ! _ ∙ _
    PVRec pvs  -> uf   -- TODO: need record info!

-- readbackPVal :: PartialVal -> IO Tm
-- readbackPVal = uf

instance PSubst Val (IO Tm) where
  psubst = \case
    Rigid h sp -> case h of
      RHLocalVar x -> applyPVal (psubst x) (reverseSpine sp) []
      RHPrim i     -> psubst sp (C.Prim i)
      RHDCon i     -> psubst sp (C.DCon i)
      RHTCon i     -> psubst sp (C.TCon i)
      RHRecTy i    -> psubst sp (C.RecTy i)
      RHRec i      -> psubst sp (C.Rec i)

-- psubst :: PSubArg => Val -> Tm
-- psubst = \case
--   Rigid h sp -> _














--------------------------------------------------------------------------------
