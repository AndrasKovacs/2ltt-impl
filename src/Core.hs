{-# options_ghc -funbox-strict-fields #-}

module Core where

import Common

type Ty = Tm

data Bind a = Bind Name a
  deriving Show

data Prim
  = Lift
  | Set
  | Prop
  | Ty
  | ValTy
  | CompTy
  | ElVal
  | ElComp
  | Id
  | Refl
  | Sym
  | Trans
  | Cong
  | Coe
  deriving Show

data Spine
  = SNil
  | SCons Spine Tm Icit
  deriving Show

data TopDefInfo = TopDefInfo
  deriving Show

data TyConInfo = TyConInfo
  deriving Show

data Tm
  = LocalVar Ix
  | TyCon {-# nounpack #-} TyConInfo Spine
  | TopDef {-# nounpack #-} TopDefInfo
  | Decl Ty Tm (Bind Tm)  -- stage 0 forward declaration
  | Let Ty Tm (Bind Tm)
  | Pi Ty (Bind Tm)
  | Prim Prim
  | App Tm Tm Icit
  | Lam
  -- | Rec -- TODO
  | Proj Tm Proj
  | Quote Tm
  | Splice Tm
  deriving Show
