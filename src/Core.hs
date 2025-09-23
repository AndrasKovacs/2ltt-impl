{-# options_ghc -funbox-strict-fields #-}

module Core where

import {-# source #-} Value (Val)

import Common

type Ty = Tm

data Bind a = Bind {
    bindName :: Name
  , bindBody :: a
  } deriving Show

data BindI a = BindI {
    bindIName :: Name
  , bindIIcit :: Icit
  , bindIBody :: a
  } deriving Show

data Prim
  = Lift
  | Set
  | Prop
  | Ty
  | ValTy
  | CompTy
  | ElVal
  | ElComp
  | Exfalso
  | Id
  | Refl
  | Sym
  | Trans
  | Cong
  | Coe
  deriving Show

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

data Tm
  = LocalVar Ix
  | TCon {-# nounpack #-} TConInfo
  | DCon {-# nounpack #-} DConInfo
  | TopDef {-# nounpack #-} DefInfo
  | Let Ty SP Tm (Bind Tm)
  | Pi Ty (BindI Tm)
  | Prim Prim
  | App Tm Tm Icit SP -- TODO: pack Icit and SP
  | Lam Ty (BindI Tm)

  | Decl Ty (Bind Tm)  -- stage 0 forward declaration
  | Let0 Ty Tm (Bind Tm)


  -- | Rec -- TODO
  -- | RecTy -- TODO

  | Proj Tm Proj SP
  | Quote Tm
  | Splice Tm

makeFields ''Bind
makeFields ''BindI
makeFields ''DefInfo
makeFields ''TConInfo
makeFields ''DConInfo

instance Show DefInfo  where show x = show (x^.name)
instance Show TConInfo where show x = show (x^.name)
instance Show DConInfo where show x = show (x^.name)
deriving instance Show Tm
