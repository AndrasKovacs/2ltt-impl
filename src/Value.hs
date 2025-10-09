
module Value where

import GHC.Word
import Common hiding (Set)
import qualified Common as C
import {-# SOURCE #-} Core (DefInfo, TConInfo, DConInfo, DCon0Info, Def0Info, RecInfo)

-- rigid heads
-- the things here can be eliminated further, but never computed
data RigidHead
  = RHLocalVar Lvl
  | RHPrim Prim
  | RHDCon  {-# nounpack #-} DConInfo
  | RHTCon  {-# nounpack #-} TConInfo
  | RHRecTy {-# nounpack #-} RecInfo
  | RHRec   {-# nounpack #-} RecInfo
  deriving Show

-- delayed unfoldings
data UnfoldHead
  = UHMeta MetaVar                          -- solved meta
  | UHTopDef {-# nounpack #-} DefInfo ~Val  -- top definition
  deriving Show

data Spine
  = SId
  | SApp Spine Val Icit
  | SProject Spine Proj
  deriving Show

instance Apply Spine Val Spine where
  {-# inline (∙) #-}
  spn ∙ v = SApp spn v Expl
  {-# inline (∘) #-}
  spn ∘ v = SApp spn v Impl

{-# inline spineApps #-}
spineApps :: Traversal' Spine (Ix, Val,Icit)
spineApps f = go 0 where
  go ix SId            = pure SId
  go ix (SApp t u i)   = (\t (!_,!u,!i) -> SApp t u i) <$> go (ix - 1) t <*> f (ix,u,i)
  go ix (SProject t p) = (\t -> SProject t p) <$> go ix t

--------------------------------------------------------------------------------

data ClosureI = ClI# {
    closureIName :: Name
  , closureIIcit :: Icit
  , closureIBody :: Val -> Val
  }

pattern ClI :: Name -> Icit -> (Val -> Val) -> ClosureI
pattern ClI x i f <- ClI# x i f where ClI x i f = ClI# x i (oneShot f)
{-# complete ClI #-}
{-# inline ClI #-}

instance Show ClosureI where showsPrec _ _ acc = "<closure>" ++ acc

instance Apply ClosureI Val Val where
  {-# inline (∙∘) #-}
  ClI _ _ f ∙∘ (!x,_) = f x

data Closure0 = Cl0# Name (Word# -> Val0)
instance Show Closure0 where showsPrec _ _ acc = "<closure>" ++ acc

pattern Cl0 x f <- ((\(Cl0# x f) -> (x,(\x -> case x of Lvl (W# x) -> f x))) -> (x, f)) where
  Cl0 x f = Cl0# x (\x -> f (Lvl (W# x)))
{-# inline Cl0 #-}
{-# complete Cl0 #-}

data Closure = Cl# {
    closureName :: Name
  , closureBody :: Val -> Val
  }

pattern Cl :: Name -> (Val -> Val) -> Closure
pattern Cl x f <- Cl# x f where Cl x f = Cl# x (oneShot f)
{-# complete Cl #-}
{-# inline Cl #-}

instance Show Closure where showsPrec _ _ acc = "<closure>" ++ acc

instance Apply Closure Val Val where
  {-# inline (∙∘) #-}
  Cl _ f ∙∘ (!x,_) = f x

instance Apply Val Val Val where
  {-# inline (∙∘) #-}
  t ∙∘ arg@(u, i) = case t of
    Lam _ t        -> t ∙ u
    Rigid h spn    -> Rigid h (spn ∙∘ arg)
    Flex h spn     -> Flex h (spn ∙∘ arg)
    Unfold h spn v -> Unfold h (spn ∙∘ arg) (v ∙∘ arg)
    _              -> impossible

--------------------------------------------------------------------------------

type VTy = Val

data Val0
  = LocalVar0 Lvl
  | TopDef0 {-# nounpack #-} Def0Info
  | DCon0   {-# nounpack #-} DCon0Info
  | App0 Val0 Val0
  | Lam0 VTy Closure0
  | Decl0 VTy Closure0
  | Project0 Val0 Proj
  | Splice Val
  deriving Show

data Val
  = Rigid RigidHead Spine
  | Flex MetaVar Spine
  | Unfold UnfoldHead Spine ~Val
  | Pi VTy ClosureI
  | Lam VTy ClosureI
  | Quote Val0
 deriving Show

--------------------------------------------------------------------------------

pattern LocalVar x = Rigid (RHLocalVar x) SId
pattern Λ x i a t = Lam a (ClI x i t)
pattern ΛE x a t = Lam a (ClI x Expl t)
pattern ΛI x a t = Lam a (ClI x Impl t)
pattern PiE x a b = Pi a (ClI x Expl b)
pattern PiI x a b = Pi a (ClI x Impl b)

pattern RecTy i sp = Rigid (RHRecTy i) sp
pattern Rec i sp = Rigid (RHRec i) sp
pattern SAppE t u = SApp t u Expl
pattern SAppI t u = SApp t u Impl

-- statically allocated constants, for sharing
sSet    = Rigid (RHPrim C.Set)    SId; {-# noinline sSet #-}
sTy     = Rigid (RHPrim C.Ty)     SId; {-# noinline sTy #-}
sValTy  = Rigid (RHPrim C.ValTy)  SId; {-# noinline sValTy #-}
sCompTy = Rigid (RHPrim C.CompTy) SId; {-# noinline sCompTy #-}

pattern Lift a     = Rigid (RHPrim C.Lift) (SId `SAppE` a)
pattern Set       <- Rigid (RHPrim C.Set)    SId where Set    = sSet
pattern Ty        <- Rigid (RHPrim C.Ty)     SId where Ty     = sTy
pattern ValTy     <- Rigid (RHPrim C.ValTy)  SId where ValTy  = sValTy
pattern CompTy    <- Rigid (RHPrim C.CompTy) SId where CompTy = sCompTy
pattern ElVal  a   = Rigid (RHPrim C.ElVal) (SId `SAppE` a)
pattern ElComp a   = Rigid (RHPrim C.ElComp) (SId `SAppE` a)
pattern Eq a x y   = Rigid (RHPrim C.Eq) (SId `SAppI` a `SAppE` x `SAppE` y)
pattern Refl a x   = Rigid (RHPrim C.Refl) (SId `SAppI` a `SAppI` x)
pattern Fun0 a b   = Rigid (RHPrim C.Fun0) (SId `SAppI` a `SAppI` b)

{-# inline Set #-}
{-# inline Ty #-}
{-# inline ValTy #-}
{-# inline CompTy #-}

infixr 1 ∙>
(∙>) a b = PiE N_ a \_ -> b
infixr 1 ∘>
(∘>) a b = PiI N_ a \_ -> b

data G    = G {g1 :: Val, g2 :: Val}
type GTy  = G
type GVal = G

gjoin :: Val -> G
gjoin v = G v v

gSet :: GTy
gSet = G Set Set

data Env = ENil | EDef Env ~Val | EDef0 Env Lvl deriving Show
type EnvArg = (?env :: Env)

instance Sized Env where
  size = go 0 where
    go acc ENil        = acc
    go acc (EDef e _)  = go (acc + 1) e
    go acc (EDef0 e _) = go (acc + 1) e

makeFields ''ClosureI
