
module Value where

import GHC.Word
import Common hiding (Set, Prop)
import qualified Common as C
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
  | RHCoe Val Val Val Val
  | RHPrim Prim
  deriving Show

-- flexible neutral heads: can be eliminated, can be unblocked
data FlexHead
  = FHMeta MetaVar
  | FHCoe MetaVar Val Val Val Val  -- coe blocked on single meta
  deriving Show

blocker :: FlexHead -> MetaVar
blocker = \case
  FHMeta m -> m
  FHCoe m _ _ _ _ -> m

-- delayed unfoldings
data UnfoldHead
  = UHMeta MetaVar                          -- solved meta
  | UHTopDef {-# nounpack #-} DefInfo ~Val  -- top definition
  | UHCoe Val Val Val Val                   -- at least one of the values is an unfolding
  deriving Show

data Spine
  = SId
  | SApp Spine Val Icit SP -- TODO: pack Icit and SP
  | SProject Spine Proj
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
  | Project0 Val0 Proj0
  | Splice Val
  deriving Show

data Val
  = Rigid RigidHead Spine
  | Flex FlexHead Spine
  | Unfold UnfoldHead Spine ~Val
  | Pi VTy SP NIClosure
  | Lam VTy NIClosure
  | Record (List Val)
  | TCon {-# nounpack #-} TConInfo (List Val)  -- fully applied
  | DCon {-# nounpack #-} DConInfo (List Val)  -- fully applied
  | Quote Val0
 deriving Show

--------------------------------------------------------------------------------

pattern Λ x i a t = Lam a (NICl x i (Cl t))

pattern PiES x a b = Pi a S (NICl x Expl (Cl b))
pattern PiEP x a b = Pi a P (NICl x Expl (Cl b))
pattern PiIS x a b = Pi a S (NICl x Impl (Cl b))
pattern PiIP x a b = Pi a P (NICl x Impl (Cl b))

pattern ΛE x a t = Lam a (NICl x Expl (Cl t))
pattern ΛI x a t = Lam a (NICl x Impl (Cl t))

pattern SAppES t u = SApp t u Expl S
pattern SAppIS t u = SApp t u Impl S
pattern SAppEP t u = SApp t u Expl P
pattern SAppIP t u = SApp t u Impl P

-- statically allocated constants, for sharing
sSet    = Rigid (RHPrim C.Set) SId; {-# noinline sSet #-}
sProp   = Rigid (RHPrim C.Prop) SId; {-# noinline sProp #-}
sTy     = Rigid (RHPrim C.Ty) SId; {-# noinline sTy #-}
sBot    = Rigid (RHPrim C.Bot) SId; {-# noinline sBot #-}
sValTy  = Rigid (RHPrim C.ValTy) SId; {-# noinline sValTy #-}
sCompTy = Rigid (RHPrim C.CompTy) SId; {-# noinline sCompTy #-}

pattern Lift a            = Rigid (RHPrim C.Lift) (SId `SAppES` a)
pattern Set              <- Rigid (RHPrim C.Set)    SId where Set    = sSet
pattern Bot              <- Rigid (RHPrim C.Bot)    SId where Bot    = sBot
pattern Prop             <- Rigid (RHPrim C.Prop)   SId where Prop   = sProp
pattern Ty               <- Rigid (RHPrim C.Ty)     SId where Ty     = sTy
pattern ValTy            <- Rigid (RHPrim C.ValTy)  SId where ValTy  = sValTy
pattern CompTy           <- Rigid (RHPrim C.CompTy) SId where CompTy = sCompTy
pattern ElVal  a          = Rigid (RHPrim C.ElVal) (SId `SAppES` a)
pattern ElComp a          = Rigid (RHPrim C.ElComp) (SId `SAppES` a)
pattern Exfalso  a t      = Rigid (RHPrim C.Exfalso) (SId `SAppIS` a `SAppEP` t)
pattern ExfalsoP a t      = Rigid (RHPrim C.ExfalsoP) (SId `SAppIS` a `SAppEP` t)
pattern Eq a x y          = Rigid (RHPrim C.Eq) (SId `SAppIS` a `SAppES` x `SAppES` y)
pattern Refl a x          = Rigid (RHPrim C.Refl) (SId `SAppIS` a `SAppIS` x)
pattern Sym a x y p       = Rigid (RHPrim C.Sym) (SId `SAppIS` a `SAppIS` x `SAppIS` y `SAppEP` p)
pattern Trans a x y z p q = Rigid (RHPrim C.Sym) (SId `SAppIS` a `SAppIS` x `SAppIS` y `SAppIS` z `SAppEP` p `SAppEP` q)
pattern Ap a b f x y p    = Rigid (RHPrim C.Ap) (SId `SAppIS` a `SAppIS` b `SAppIS` f `SAppIS` x `SAppIS` y `SAppEP` p)
pattern Fun0 a b          = Rigid (RHPrim C.Fun0) (SId `SAppIS` a `SAppIS` b)
pattern PropExt a b f g   = Rigid (RHPrim C.PropExt) (SId `SAppIS` a `SAppIS` b `SAppEP` f `SAppEP` g)
pattern FunExt a b f g p  = Rigid (RHPrim C.FunExt) (SId `SAppIS` a `SAppIS` b `SAppES` f `SAppES` g `SAppEP` p)
pattern FunExtP a b f g p = Rigid (RHPrim C.FunExtP) (SId `SAppIS` a `SAppIS` b `SAppES` f `SAppES` g `SAppEP` p)

{-# inline Set #-}
{-# inline Prop #-}
{-# inline Ty #-}
{-# inline ValTy #-}
{-# inline CompTy #-}

pattern RCoe a b p x = Rigid (RHCoe a b p x) SId
pattern FCoe m a b p x = Flex (FHCoe m a b p x) SId

{-# inline UCoe #-}
pattern UCoe a b p x v <- Unfold (UHCoe a b p x) SId v where
  UCoe a b p x ~v = Unfold (UHCoe a b p x) SId v

infixr 1 ∙∙>
(∙∙>) :: Val -> Val -> Val
(∙∙>) a b = PiES N_ a \_ -> b

infixr 1 ∙∘>
(∙∘>) :: Val -> Val -> Val
(∙∘>) a b = PiEP N_ a \_ -> b

infixr 1 ∘∙>
(∘∙>) :: Val -> Val -> Val
(∘∙>) a b = PiIS N_ a \_ -> b

infixr 1 ∘∘>
(∘∘>) :: Val -> Val -> Val
(∘∘>) a b = PiIP N_ a \_ -> b

data G = G {g1 :: Val, g2 :: Val}

gjoin :: Val -> G
gjoin v = G v v

spVal :: SP -> Val
spVal S = Set
spVal P = Prop

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
