
module Elaboration where

import Core.Syntax (Tm)
import Core.Value (Val)

-- Required by Unification

retryProblem :: Int -> IO ()
retryAllProblems :: IO ()

-- Required by Elaboration.State
data Check = Check Tm ~Val
