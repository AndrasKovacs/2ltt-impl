{-# options_ghc -funbox-strict-fields #-}

module Value where

import GHC.Word
import Common
import {-# SOURCE #-} Core (TyConInfo)

-- rigid neutral heads
-- the things here can be eliminated further, but never computed
data RigidHead
  = RHLocalVar Lvl
  | RHCoe Val Val Val Val
  | RHExfalso Val Val
  | RHRefl Val Val
  | RHSym Val Val Val Val
  | RHTrans Val Val Val Val Val Val
  | RHAp Val Val Val Val Val Val
  deriving Show

-- flexible neutral heads: can be eliminated, can be unblocked
data FlexHead
  = FHMeta MetaVar
  | FHCoe MetaVar Val Val Val Val  -- coe blocked on meta
  deriving Show

-- delayed unfoldings
data UnfoldHead
  = UHMeta MetaVar        -- solved meta
  | UHTopDef Lvl ~Val     -- top definition
  | UHCoe Val Val Val Val -- at least one of the values is an unfolding
  deriving Show

data Spine
  = SId
  | SApp Spine Val Icit
  | SProj Spine Proj
  deriving Show

--------------------------------------------------------------------------------

-- | A closure abstracts over the `Int#` which marks the next fresh variable.
--   Since it is impossible for GHC to unbox this argument, and we want to make
--   the argument implicit, and only lifted types can be implicit, we unbox it
--   by hand, and define `Cl` as a pattern synonym with the more convenient
--   type.
newtype Closure = Cl# {unCl# :: Word# -> Val -> Val}
newtype Wrap# = Wrap# (LvlArg => Val -> Val)

pattern Cl :: (LvlArg => Val -> Val) -> Closure
pattern Cl f <- ((\(Cl# f) -> Wrap# \v -> case ?lvl of Lvl (W# l) -> f l v) -> Wrap# f) where
  Cl f = Cl# (oneShot \l -> lam1 \v -> let ?lvl = Lvl (W# l) in f v)
{-# complete Cl #-}
{-# inline Cl #-}

infixl 8 ∘
infixl 8 ∘~
class Apply a b c | a -> b c where
  (∘)  :: LvlArg => a -> b -> c  -- call by value
  (∘~) :: LvlArg => a -> b -> c  -- lazy

instance Show Closure where showsPrec _ _ acc = "<closure>" ++ acc

instance (b ~ Val, c ~ Val) => Apply Closure b c where
  {-# inline (∘) #-}
  Cl f ∘ x = f x
  {-# inline (∘~) #-}
  Cl f ∘~ ~x = f x

data NamedClosure = PCl {
    namedClosureName    :: Name
  , namedClosureIcit    :: Icit
  , namedClosureClosure :: Closure
  } deriving Show

instance Apply NamedClosure Val Val where
  {-# inline (∘) #-}
  PCl _ _ (Cl f) ∘ x = f x
  {-# inline (∘~) #-}
  PCl _ _ (Cl f) ∘~ ~x = f x

--------------------------------------------------------------------------------

type Ty = Val

data Val
  = Rigid RigidHead Spine
  | Flex FlexHead Spine
  | Unfold UnfoldHead Spine

  -- canonicals
  | Set
  | Prop
  | Bot
  | Eq Val Val Val
  | Pi Ty NamedClosure
  | Lam Ty NamedClosure
  | RecTy {-# nounpack #-} TyConInfo Spine
  | Rec {-# nounpack #-} TyConInfo Spine
 deriving Show
