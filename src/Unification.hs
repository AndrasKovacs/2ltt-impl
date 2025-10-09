
module Unification where

import Common
import Core (Ty, Tm, Locals, LocalsArg)
import qualified Core as C
import Value
import qualified Elaboration.State as ES
import Evaluation

-- closeTy :: LocalsArg => Ty -> Ty
-- closeTy a = _

-- -- TODO: optimize
-- freshMeta :: LvlArg => LocalsArg => VTy -> IO Tm
-- freshMeta a = do
--   let closed = eval0 $ closeTy $ readBack0 UnfoldNone a
--   m <- ES.newMeta closed
--   pure $ C.Meta m
