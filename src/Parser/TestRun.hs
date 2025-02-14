
module Parser.TestRun where

import Common
import qualified FlatParse.Stateful as FP
import Parser.Test

foo :: Parser Span
foo = $(sym "blabar")
