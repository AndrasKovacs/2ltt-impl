
module Core.Info where

import Common
import {-# source #-} Core.Value
import {-# source #-} Core.Syntax

data FieldInfo
  = FINil
  | FISnoc FieldInfo Name Icit Ty
  deriving Show

data DefInfo = DI {
    defInfoUid   :: Int
  , defInfoValue :: ~Val
  , defInfoName  :: Name
  }

data RecInfo = RI {
    recInfoUid       :: Int
  , recInfoValue     :: ~Val
  , recInfoName      :: Name
  , recInfoFields    :: FieldInfo
  }

data TConInfo = TCI {
    tConInfoUid   :: Int
  , tConInfoValue :: ~Val
  , tConInfoName  :: Name
  }

data DConInfo = DCI {
    dConInfoUid   :: Int
  , dConInfoValue :: ~Val
  , dConInfoName  :: Name
  }

data Def0Info = D0I {
    def0InfoUid   :: Int
  , def0InfoName  :: Name
  }

data Rec0Info = R0I {
    rec0InfoUid   :: Int
  , rec0InfoName  :: Name
  }

data TCon0Info = TC0I {
    tCon0InfoUid   :: Int
  , tCon0InfoName  :: Name
  }

data DCon0Info = DC0I {
    dCon0InfoUid   :: Int
  , dCon0InfoName  :: Name
  }

makeFields ''DefInfo
makeFields ''RecInfo
makeFields ''TConInfo
makeFields ''DConInfo
makeFields ''Def0Info
makeFields ''Rec0Info
makeFields ''TCon0Info
makeFields ''DCon0Info
instance Show DefInfo   where show x = show (x^.name)
instance Show RecInfo   where show x = show (x^.name)
instance Show TConInfo  where show x = show (x^.name)
instance Show DConInfo  where show x = show (x^.name)
instance Show Def0Info  where show x = show (x^.name)
instance Show Rec0Info  where show x = show (x^.name)
instance Show TCon0Info where show x = show (x^.name)
instance Show DCon0Info where show x = show (x^.name)
instance Eq DefInfo   where x == y = x^.uid == y^.uid
instance Eq RecInfo   where x == y = x^.uid == y^.uid
instance Eq TConInfo  where x == y = x^.uid == y^.uid
instance Eq DConInfo  where x == y = x^.uid == y^.uid
instance Eq Def0Info  where x == y = x^.uid == y^.uid
instance Eq Rec0Info  where x == y = x^.uid == y^.uid
instance Eq TCon0Info where x == y = x^.uid == y^.uid
instance Eq DCon0Info where x == y = x^.uid == y^.uid
