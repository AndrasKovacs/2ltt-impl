
module Errors where

import Control.Exception
import Data.ByteString qualified as B
import FlatParse.Stateful qualified as FP

import Common
import Core.Value
import Core.Syntax
import Presyntax qualified as P
import Unification
import Pretty
import Evaluation

data Error
  = UnifyError Val Val UnifyEx
  | MissingAnnotation
  | Generic String

instance IsString Error where
  fromString = Generic

data ErrorInCxt = ErrorInCxt Src Locals Lvl P.Tm Error

instance Show ErrorInCxt where
  show (ErrorInCxt src ls l t err) =
    let ?locals = ls
        ?lvl = l in
    let showVal :: Val -> String
        showVal v = pretty (readBack (localsLength ls) UnfoldMetas v) in
    -- TODO
    let msg = case err of
          MissingAnnotation -> "Missing type annotation"
          Generic s -> s
          UnifyError t u ex ->
               "Can't unify inferred type\n\n  "
               ++ showVal t ++ "\n\nwith expected type\n\n  " ++ showVal u ++ "\n"

    in render (srcToBs src) (spanOf t) msg

instance Exception ErrorInCxt

-- | Display an error with source position. We only use of the first position in
--   the span.
render :: B.ByteString -> Span -> String -> String
render bs (Span pos _) msg = let
  ls     = FP.linesUtf8 bs
  (l, c) = case FP.posLineCols bs [coerce pos] of [x] -> x; _ -> impossible
  line   = if l < length ls then ls !! l else ""
  linum  = show (l + 1)
  lpad   = map (const ' ') linum
  in linum  ++ ":" ++ show c ++ ":\n" ++
     lpad   ++ "|\n" ++
     linum  ++ "| " ++ line ++ "\n" ++
     lpad   ++ "| " ++ replicate c ' ' ++ "^\n" ++
     msg
{-# noinline render #-}
