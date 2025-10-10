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
- Libal-Miller unification:
  Not easy to properly support & combine with nested unification.
  We'd need to check overlap of every inversion, including nested inversion.
  Examples that should fail to invert because of overlap:

     ?0 (F (λ x y. f y x)) (λ x y. f y x)
     ?0 (F f) f
     ?0 (F f) (λ x. f (x.1, x.2))

  How do I effectively check overlap?
    - Try to invert every subterm of a Libal-Miller-inverted term, mapping
      all of them to TOP. The point is that once we did LM inversion, inversion
      is forbidden for all subterms.
    - Doesn't sound too difficult, but it's expensive
-}

--------------------------------------------------------------------------------

freshMeta :: LocalsArg => Ty -> IO Tm
freshMeta a = do
  m <- ES.newMeta a
  pure $ C.Meta m C.MSId

--------------------------------------------------------------------------------

-- ^ These closures abstract over all enclosing lambda binders in a PartialValue.
newtype PClosure = PCl (List Val -> Val)

instance Show PClosure where showsPrec _ _ acc = "<closure>" ++ acc

instance Apply PClosure (List Val) Val where
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
  , partialSubAllowPruning :: Bool
  , partialSubDom          :: Lvl                  -- ^ Domain (size of the map)
  , partialSubCod          :: Lvl                  -- ^ Codomain (next fresh Lvl)
  , partialSubSub          :: IntMap PartialVal
  }
makeFields ''PartialSub

type PSubArg = (?psub :: PartialSub)

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
lift (PSub occ pr dom cod sub) =
  PSub occ pr (dom + 1) (cod + 1) $
    IM.insert (fromIntegral cod) (PVVal $ PCl \_ -> LocalVar dom) sub

update :: Lvl -> Path -> PClosure -> PartialSub -> PartialSub
update x path def psub =
  let ~newpv = extendPVal path def PVBot in
  psub & sub %~ IM.insertWith (\_ -> extendPVal path def) (fromIntegral x) newpv

class PSubst a b | a -> b where
  psubst :: PSubArg => a -> b

instance PSubst Val Tm where
  psubst = \case
    Rigid h sp -> _

-- psubst :: PSubArg => Val -> Tm
-- psubst = \case
--   Rigid h sp -> _














--------------------------------------------------------------------------------
