
module Core.Syntax where

import Common
import Core.Info

data Tm0
  = LocalVar0 Ix
  | Meta0 MetaVar MetaSub
  | TopDef0 {-# nounpack #-} Def0Info
  | DCon0   {-# nounpack #-} DCon0Info
  | Rec0    {-# nounpack #-} Rec0Info
  | Project0 Tm0 Proj
  | CProject Tm0 Proj
  | App0 Tm0 Tm0
  | Lam0 (Bind Tm0)
  | Let0 Tm0 (Bind Tm0)
  | Decl0 (Bind Tm0)
  | Splice Tm

type Ty = Tm

data TmEnv
  = TENil
  | TEDef TmEnv Tm
  | TEBind TmEnv Tm
  | TEBind0 TmEnv Tm0

data MetaSub
  = MSId
  | MSSub TmEnv

data Tm
  = LocalVar Ix
  | TCon   {-# nounpack #-} TConInfo
  | DCon   {-# nounpack #-} DConInfo
  | Rec    {-# nounpack #-} RecInfo
  | RecTy  {-# nounpack #-} RecInfo
  | TopDef {-# nounpack #-} DefInfo
  | Meta MetaVar MetaSub
  | Let Tm (Bind Tm)
  | Pi (BindI Tm)
  | Prim Prim
  | App Tm Tm Icit
  | Lam (BindI Tm)
  | Project Tm Proj
  | Quote Tm0
  | Wk Tm -- ^ Explicit weakening over a stage 1 bound var.

instance Apply Tm Tm Tm where
  {-# inline (∙∘) #-}
  (∙∘) t (u,i) = App t u i

pattern AppE t u = App t u Expl
pattern AppI t u = App t u Impl

{-# inline quote #-}
quote :: Tm0 -> Tm
quote = \case Core.Syntax.Splice t -> t; t -> Core.Syntax.Quote t

{-# inline splice #-}
splice :: Tm -> Tm0
splice = \case Core.Syntax.Quote t -> t; t -> Core.Syntax.Splice t

deriving instance Show TmEnv
deriving instance Show MetaSub
deriving instance Show Tm
deriving instance Show Tm0

pattern Set :: Tm
pattern Set = Prim Common.Set

data Locals
  = LNil
  | LDef Locals Name Tm Ty
  | LBind Locals Name ~Ty
  | LBind0 Locals Name ~Ty
  deriving Show

type LocalsArg = (?locals :: Locals)

{-# inline setLocals #-}
setLocals :: Locals -> (LocalsArg => a) -> a
setLocals ls act = let ?locals = ls in act

localsLength :: Locals -> Lvl
localsLength = go 0 where
  go acc LNil = acc
  go acc (LDef ls _ _ _) = go (acc + 1) ls
  go acc (LBind ls _ _)  = go (acc + 1) ls
  go acc (LBind0 ls _ _) = go (acc + 1) ls

localsToNames :: Locals -> Names
localsToNames = \case
  LNil          -> Nil
  LDef ls x _ _ -> Cons x (localsToNames ls)
  LBind0 ls x _ -> Cons x (localsToNames ls)
  LBind ls x _  -> Cons x (localsToNames ls)
