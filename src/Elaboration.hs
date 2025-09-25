
module Elaboration where

import Common
import Core (Tm, Ty, Tm0)
import Value (Val, Val0, VTy, G, EnvArg, GTy)
import Evaluation

import qualified Presyntax as P
import qualified Common as C
import qualified Core as C
import qualified Value as V

type Elab a = LvlArg => EnvArg => a

check :: Elab (P.Tm -> GTy -> SP -> IO Tm)
check t a as = uf

infer :: Elab (P.Tm -> SP -> IO (Tm, GTy))
infer t s = uf

check0 :: Elab (P.Tm -> GTy -> IO Tm0)
check0 = uf

infer0 :: Elab (P.Tm -> IO (Tm0, GTy))
infer0 = uf
