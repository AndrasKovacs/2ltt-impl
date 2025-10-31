
module Core.Syntax where

import Common
import Core.Info

data Tm0
  = LocalVar0 Ix
  | Meta0 MetaVar MetaSub
  | TopDef0 {-# nounpack #-} Def0Info
  | DCon0   {-# nounpack #-} DCon0Info
  | Project0 Tm0 Proj
  | App0 Tm0 Tm0
  | Lam0 (Bind Tm0)
  | Let0 Tm0 (Bind Tm0)
  | Decl0 (Bind Tm0)
  | Splice Tm

type Ty = Tm

data TmEnv
  = TENil
  | TELet TmEnv Tm
  | TEDef TmEnv Tm
  | TEDef0 TmEnv Ix

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

data Locals
  = LNil
  | LDef Locals Name Tm Ty
  | LBind Locals Name Ty
  | LBind0 Locals Name Ty
  deriving Show

type LocalsArg = (?locals :: Locals)
