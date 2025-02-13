
module Parser.Test where

import qualified FlatParse.Stateful as FP
import Data.Char
import Parser.Batteries

-- TODO: recognize operator chunk tokens

config :: Config
config = Config {
    _configFirstIdentChar    = [|| FP.satisfy isLetter ||]
  , _configRestIdentChar     = [|| FP.satisfy (\c -> c == '\'' || isAlphaNum c) ||]
  , _configWhitespaceChars   = " \t\r\v\f" -- ASCII whitespace only
  , _configLineComment       = "--"
  , _configBlockCommentStart = "{-"
  , _configBlockCommentEnd   = "-}"
  , _configKeywords          = _
  }
