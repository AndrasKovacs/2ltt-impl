{-# options_ghc -funbox-strict-fields #-}

module Core where

import {-# source #-} Value (Val)

import Common

data Bind a = Bind {
    bindName :: Name
  , bindBody :: a
  } deriving Show

data BindI a = BindI {
    bindIName :: Name
  , bindIIcit :: Icit
  , bindIBody :: a
  } deriving Show

data DefInfo = DI {
    defInfoValue :: ~Val
  , defInfoName  :: Name
  }

data TConInfo = TCI {
    tConInfoValue :: ~Val
  , tConInfoName  :: Name
  }

data DConInfo = DCI {
    dConInfoValue :: ~Val
  , dConInfoName  :: Name
  }

data Def0Info = D0I {
    def0InfoName  :: Name
  }

data TCon0Info = TC0I {
    tCon0InfoName  :: Name
  }

data DCon0Info = DC0I {
    dCon0InfoName  :: Name
  }

data Tm0
  = LocalVar0 Ix
  | TopDef0 {-# nounpack #-} Def0Info
  | DCon0   {-# nounpack #-} DCon0Info
  | Record0 (List Tm0)
  | Proj0 Tm0 Proj
  | App0 Tm0 Tm0
  | Lam0 Ty (Bind Tm0)
  | Decl0 Ty (Bind Tm0)
  | Splice Tm

data Prim
  = Lift
  | Set
  | Prop
  | Ty
  | ValTy
  | CompTy
  | ElVal
  | ElComp
  | Exfalso SP
  | Eq
  | Refl
  | Sym
  | Trans
  | Ap
  | Coe
  deriving Show

type Ty = Tm

data Tm
  = LocalVar Ix
  | TCon   {-# nounpack #-} TConInfo
  | DCon   {-# nounpack #-} DConInfo
  | TopDef {-# nounpack #-} DefInfo
  | Let Ty SP Tm (Bind Tm)
  | Fun0 Ty Ty
  | Record (List Tm)
  | Pi Ty (BindI Tm)
  | Prim Prim
  | App Tm Tm Icit SP -- TODO: pack Icit and SP
  | Lam Ty (BindI Tm)
  | Proj Tm Proj SP
  | Quote Tm0

makeFields ''Bind
makeFields ''BindI
makeFields ''DefInfo
makeFields ''TConInfo
makeFields ''DConInfo
makeFields ''Def0Info
makeFields ''TCon0Info
makeFields ''DCon0Info

instance Show DefInfo   where show x = show (x^.name)
instance Show TConInfo  where show x = show (x^.name)
instance Show DConInfo  where show x = show (x^.name)
instance Show Def0Info  where show x = show (x^.name)
instance Show TCon0Info where show x = show (x^.name)
instance Show DCon0Info where show x = show (x^.name)
deriving instance Show Tm
deriving instance Show Tm0
