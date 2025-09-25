
module Elaboration.State where

import qualified Data.Array.Dynamic.L as ADL
import Common
import Core (Tm)
import qualified Core as C
import Value (Val)
import qualified Value as V

-- data Solved = Solved {
--     solvedLocals           :: C.Locals
--   , solvedSolution         :: Tm
--   , solvedSolutionVal      :: Val
--   , solvedTy               :: Ty
--   , solvedIsInlinable      :: Bool
--   }

-- data MetaEntry
--   = MEUnsolved Unsolved
