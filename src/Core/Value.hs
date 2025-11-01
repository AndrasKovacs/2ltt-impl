
module Core.Value where

import GHC.Word
import Common hiding (Set)
import qualified Common as C
import Core.Info

-- rigid heads
-- the things here can be eliminated further, but never computed
data RigidHead
  = RHLocalVar Lvl ~VTy
  | RHPrim Prim
  | RHDCon  {-# nounpack #-} DConInfo
  | RHTCon  {-# nounpack #-} TConInfo
  | RHRecTy {-# nounpack #-} RecInfo
  | RHRec   {-# nounpack #-} RecInfo
  deriving Show

data MetaHead = MetaHead MetaVar Env
  deriving Show

-- delayed unfoldings
data UnfoldHead
  = UHMeta MetaHead
  | UHTopDef {-# nounpack #-} DefInfo
  | UHLocalDef Lvl
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

-- reversed
data RevSpine
  = RSId
  | RSApp Val Icit RevSpine
  | RSProject Proj RevSpine
  deriving Show

reverseSpine :: Spine -> RevSpine
reverseSpine = go RSId where
  go acc SId            = acc
  go acc (SApp t u i)   = go (RSApp u i acc) t
  go acc (SProject t p) = go (RSProject p acc) t

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
  , closureITy   :: ~VTy
  , closureIBody :: Val -> Val
  }

pattern ClI :: Name -> Icit -> VTy -> (Val -> Val) -> ClosureI
pattern ClI x i a f <- ClI# x i a f where ClI x i ~a f = ClI# x i a (oneShot f)
{-# complete ClI #-}
{-# inline ClI #-}

instance Show ClosureI where showsPrec _ _ acc = "<closure>" ++ acc

instance Apply ClosureI Val Val where
  {-# inline (∙∘) #-}
  ClI _ _ _ f ∙∘ (!x,_) = f x

data Closure0 = Cl0# Name VTy (Word# -> Val0)
instance Show Closure0 where showsPrec _ _ acc = "<closure>" ++ acc

pattern Cl0 x a f <- ((\(Cl0# x a f) -> (x, a, (\x -> case x of Lvl (W# x) -> f x))) -> (x, a, f)) where
  Cl0 x a f = Cl0# x a (\x -> f (Lvl (W# x)))
{-# inline Cl0 #-}
{-# complete Cl0 #-}

data Closure = Cl# {
    closureName :: Name
  , closureTy   :: VTy
  , closureBody :: Val -> Val
  }

pattern Cl :: Name -> VTy -> (Val -> Val) -> Closure
pattern Cl x a f <- Cl# x a f where Cl x a f = Cl# x a (oneShot f)
{-# complete Cl #-}
{-# inline Cl #-}

instance Show Closure where showsPrec _ _ acc = "<closure>" ++ acc

instance Apply Closure Val Val where
  {-# inline (∙∘) #-}
  Cl _ _ f ∙∘ (!x,_) = f x

instance Apply Val Val Val where
  {-# inline (∙∘) #-}
  t ∙∘ arg@(u, i) = case t of
    Lam t          -> t ∙ u
    Rigid h spn    -> Rigid h (spn ∙∘ arg)
    Flex h spn     -> Flex h (spn ∙∘ arg)
    Unfold h spn v -> Unfold h (spn ∙∘ arg) (v ∙∘ arg)
    _              -> impossible

--------------------------------------------------------------------------------

type VTy = Val

data Val0
  = LocalVar0 Lvl
  | Meta0 MetaHead
  | SolvedMeta0 MetaHead ~Val0
  | TopDef0 {-# nounpack #-} Def0Info
  | DCon0   {-# nounpack #-} DCon0Info
  | App0 Val0 Val0
  | Lam0 Closure0
  | Decl0 Closure0
  | Let0 Val0 Closure0
  | Project0 Val0 Proj
  | Splice Val
  deriving Show

data Val
  = Rigid RigidHead Spine
  | Flex {-# nounpack #-} MetaHead Spine
  | Unfold UnfoldHead Spine ~Val
  | Pi ClosureI
  | Lam ClosureI
  | Quote Val0
 deriving Show

--------------------------------------------------------------------------------

pattern LocalVar x a <- Rigid (RHLocalVar x a) SId where
  LocalVar x ~a = Rigid (RHLocalVar x a) SId

pattern Λ x i a t = Lam (ClI x i    a t)
pattern ΛE x a t  = Lam (ClI x Expl a t)
pattern ΛI x a t  = Lam (ClI x Impl a t)
pattern PiE x a b = Pi  (ClI x Expl a b)
pattern PiI x a b = Pi  (ClI x Impl a b)

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

data Env
  = ENil
  | ELet Env  Val -- ^ Let-definition in outer local scope
                  --   NOTE: the value here is already the Unfold that we want to lookup!
                  --   To get the definition body, we have to project from the Unfold.
  | EDef Env ~Val -- ^ Meta-stage binder
  | EDef0 Env Lvl -- ^ Object binder, only supports renaming.
  deriving Show

type EnvArg = (?env :: Env)

{-# inline setEnv #-}
setEnv :: Env -> (EnvArg => a) -> a
setEnv e act = let ?env = e in act

envTail :: Env -> Env
envTail (EDef e _) = e
envTail _          = impossible

instance Sized Env where
  size = go 0 where
    go acc ENil        = acc
    go acc (EDef e _)  = go (acc + 1) e
    go acc (ELet e _)  = go (acc + 1) e
    go acc (EDef0 e _) = go (acc + 1) e

makeFields ''ClosureI
