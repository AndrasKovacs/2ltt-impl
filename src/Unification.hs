{-# options_ghc -Wno-unused-imports #-}

module Unification where

import Common
import Core (Ty, Tm, Locals, LocalsArg)
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
  | PVRec (List PartialVal)
  deriving Show

data Path
  = PNil
  | PApp PClosure Icit Path
  | PProj Proj Path
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

  mkRec :: Ix -> Path -> List PartialVal
  mkRec i path = case i of
    0 -> Cons (go path PVBot) Nil
    i -> Cons PVBot (mkRec (i - 1) path)

  updRec :: Ix -> Path -> List PartialVal -> List PartialVal
  updRec i path pvs = case (i, pvs) of
    (0, Cons pv pvs) -> Cons (go path pv) pvs
    (0, Nil        ) -> Cons (go path PVBot) Nil
    (i, Cons pv pvs) -> Cons pv (updRec (i - 1) path pvs)
    (i, Nil        ) -> Cons pv (updRec (i - 1) path Nil)

  go :: Path -> PartialVal -> PartialVal
  go path pv = case (path, pv) of
    (PNil         , PVBot     ) -> PVVal def
    (PApp _ _ path, PVLam a pv) -> PVLam a (go path pv)
    (PProj p path , PVRec pvs ) -> PVRec (updRec (p^.index) path pvs)
    (PApp a i path, PVBot     ) -> PVLam a (go path PVBot)
    (PProj p path , PVBot     ) -> PVRec (mkRec (p^.index) path)
    _                           -> PVTop

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
  readb = _

instance ReadBack PartialVal ([Val] -> IO Tm) where
  readb pv args = case pv of
    PVTop      -> unifyError
    PVBot      -> unifyError
    PVVal v    -> pure $! readb (v ∙ args)
    PVLam a pv -> uf
    PVRec pvs  -> _   -- TODO: need record info!

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
