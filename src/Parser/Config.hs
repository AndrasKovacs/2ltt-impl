
module Parser.Config where

import qualified FlatParse.Stateful as FP
import Data.Char
import Parser.Batteries

config :: Config
config = Config {
    _firstIdentChar    = [|| FP.satisfy isLetter ||]
  , _restIdentChar     = [|| FP.satisfy (\c -> c == '\'' || isAlphaNum c) ||]
  , _operatorChar      = [|| FP.satisfy isSymbol ||]
  , _whitespaceChars   = " \t\r\v\f" -- ASCII whitespace only
  , _lineComment       = "--"
  , _blockCommentStart = "{-"
  , _blockCommentEnd   = "-}"
  , _symbols           = ["foo", "bar", "blabar"]
  }
