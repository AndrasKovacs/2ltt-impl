{-# options_ghc -funbox-strict-fields #-}

module Value where

import GHC.Word
import Common
import {-# SOURCE #-} Core (DefInfo, TConInfo, DConInfo, DCon0Info, Def0Info)

infixl 8 ∘
infixl 8 ∘~
class Apply a b c | a -> b c where
  (∘)  :: LvlArg => a -> b -> c  -- strict
  (∘~) :: LvlArg => a -> b -> c  -- lazy
  (∘~) = (∘)

-- rigid heads
-- the things here can be eliminated further, but never computed
data RigidHead
  = RHLocalVar Lvl
  | RHCoe
  | RHExfalso SP
  | RHRefl
  | RHSym
  | RHTrans
  | RHAp
  | RHEq
  | RHLift
  | RHElVal
  | RHElComp
  deriving Show

-- flexible neutral heads: can be eliminated, can be unblocked
data FlexHead
  = FHMeta MetaVar
  | FHCoe MetaVar Val Val Val Val  -- coe blocked on single meta
  deriving Show

-- delayed unfoldings
data UnfoldHead
  = UHMeta MetaVar                          -- solved meta
  | UHTopDef {-# nounpack #-} DefInfo ~Val  -- top definition
  | UHCoe Val Val Val Val                   -- at least one of the values is an unfolding
  deriving Show

data Spine
  = SId
  | SApp Spine Val Icit SP -- TODO: pack Icit and SP
  | SProj Spine Proj SP
  deriving Show

instance Apply Spine (Val,Icit,SP) Spine where
  {-# inline (∘) #-}
  spn ∘ (v,i,sp) = SApp spn v i sp

--------------------------------------------------------------------------------

-- | A closure abstracts over the `Int#` which marks the next fresh variable.
--   Since it is impossible for GHC to unbox this argument, and we want to make
--   the argument implicit, and only lifted types can be implicit, we unbox it
--   by hand, and define `Cl` as a pattern synonym with the more convenient
--   type.
newtype Closure = Cl# {unCl# :: Word# -> Val -> Val}
newtype Wrap# = Wrap# (LvlArg => Val -> Val)

pattern Cl :: (LvlArg => Val -> Val) -> Closure
pattern Cl f <- ((\(Cl# f) -> Wrap# (oneShot \v -> case ?lvl of Lvl (W# l) -> f l v)) -> Wrap# f)
  where Cl f = Cl# (oneShot \l -> lam1 \v -> let ?lvl = Lvl (W# l) in f v)
{-# complete Cl #-}
{-# inline Cl #-}

instance Show Closure where showsPrec _ _ acc = "<closure>" ++ acc

instance (b ~ Val, c ~ Val) => Apply Closure b c where
  {-# inline (∘) #-}
  Cl f ∘ x = f x
  {-# inline (∘~) #-}
  Cl f ∘~ ~x = f x

data NIClosure = NICl {
    nIClosureName    :: Name
  , nIClosureIcit    :: Icit
  , nIClosureClosure :: Closure
  } deriving Show

instance Apply NIClosure Val Val where
  {-# inline (∘) #-}
  NICl _ _ (Cl f) ∘ x = f x
  {-# inline (∘~) #-}
  NICl _ _ (Cl f) ∘~ ~x = f x

data NClosure = NCl {
    nClosureName    :: Name
  , nClosureClosure :: Closure
  } deriving Show

instance Apply NClosure Val Val where
  {-# inline (∘) #-}
  NCl _ (Cl f) ∘ x = f x
  {-# inline (∘~) #-}
  NCl _ (Cl f) ∘~ ~x = f x

data Closure0 = Cl0# Name (Word# -> Val0)
instance Show Closure0 where showsPrec _ _ acc = "<closure>" ++ acc

pattern Cl0 x f <- ((\(Cl0# x f) -> (x,(\x -> case x of Lvl (W# x) -> f x))) -> (x, f)) where
  Cl0 x f = Cl0# x (\x -> f (Lvl (W# x)))
{-# inline Cl0 #-}
{-# complete Cl0 #-}

--------------------------------------------------------------------------------

type VTy = Val

data Val0
  = LocalVar0 Lvl
  | TopDef0 {-# nounpack #-} Def0Info
  | DCon0   {-# nounpack #-} DCon0Info
  | App0 Val0 Val0
  | Lam0 VTy Closure0
  | Decl0 VTy Closure0
  | Record0 (List Val0)
  | Proj0 Val0 Proj
  | Splice Val
  deriving Show

data Val
  = Rigid RigidHead Spine
  | Flex FlexHead Spine
  | Unfold UnfoldHead Spine ~Val

  -- canonicals
  | Set
  | Prop
  | Bot
  | Ty
  | ValTy
  | CompTy
  | Fun0 VTy VTy
  | Pi VTy NIClosure
  | Lam VTy NIClosure
  | Record (List Val)
  | TCon {-# nounpack #-} TConInfo (List Val)  -- fully applied
  | DCon {-# nounpack #-} DConInfo (List Val)  -- fully applied
  | Quote Val0

 deriving Show

--------------------------------------------------------------------------------

pattern PiE x a b = Lam a (NICl x Expl (Cl b))
pattern PiI x a b = Lam a (NICl x Impl (Cl b))

pattern LamE x a t = Lam a (NICl x Expl (Cl t))
pattern LamI x a t = Lam a (NICl x Impl (Cl t))

pattern SAppES t u = SApp t u Expl S
pattern SAppIS t u = SApp t u Impl S
pattern SAppEP t u = SApp t u Expl P
pattern SAppIP t u = SApp t u Impl P

pattern Lift   a = Rigid RHLift   (SId `SAppES` a)
pattern ElVal  a = Rigid RHElVal  (SId `SAppES` a)
pattern ElComp a = Rigid RHElComp (SId `SAppES` a)

pattern Exfalso  a t = Rigid (RHExfalso S) (SId `SAppIS` a `SAppEP` t)
pattern ExfalsoP a t = Rigid (RHExfalso P) (SId `SAppIS` a `SAppEP` t)

pattern Eq a x y = Rigid RHEq (SId `SAppIS` a `SAppES` x `SAppES` y)
pattern Refl a x = Rigid RHRefl (SId `SAppIS` a `SAppIS` x)
pattern Sym a x y p = Rigid RHSym (SId `SAppIS` a `SAppIS` x `SAppIS` y `SAppEP` p)

pattern Trans a x y z p q =
  Rigid RHSym (SId `SAppIS` a `SAppIS` x `SAppIS` y `SAppIS` z `SAppEP` p `SAppEP` q)

pattern Ap a b f x y p =
  Rigid RHSym (SId `SAppIS` a `SAppIS` b `SAppIS` f `SAppIS` x `SAppIS` y `SAppEP` p)

pattern Coe a b p x =
  Rigid RHCoe (SId `SAppIS` a `SAppIS` b `SAppEP` p `SAppES` x)


infixr 1 ==>
(==>) :: Val -> Val -> Val
(==>) a b = PiE N_ a \_ -> b

data G = G {g1 :: Val, g2 :: Val}

gjoin :: Val -> G
gjoin v = G v v

sp :: SP -> Val
sp S = Set
sp P = Prop

data Env = ENil | EDef Env ~Val | EDef0 Env Lvl deriving Show
type EnvArg = (?env :: Env)

instance Sized Env where
  size = go 0 where
    go acc ENil        = acc
    go acc (EDef e _)  = go (acc + 1) e
    go acc (EDef0 e _) = go (acc + 1) e

--------------------------------------------------------------------------------

makeFields ''NIClosure
makeFields ''NClosure
