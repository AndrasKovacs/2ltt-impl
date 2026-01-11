
module Unification where

import Common
import Core.Value

data Convert
  = ConvYes
  | ConvNo
  | ConvBlocked MetaSet

instance Show Convert

convert :: LvlArg => Val -> Val -> Convert