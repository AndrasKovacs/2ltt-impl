
module Parser.Config (config) where

import qualified FlatParse.Stateful as FP
import Data.Char
import Parser.Batteries

config :: Config
config = Config {
    _lexicalSwitch     = '#'
  , _whitespaceChars   = " \t\r\v\f"
  , _firstIdentChar    = [|| FP.satisfy isFirstIdentChar ||]
  , _restIdentChar     = [|| FP.satisfy isRestIdentChar ||]
  , _firstOpChar       = [|| FP.satisfy isFirstOpChar ||]
  , _restOpChar        = [|| FP.satisfy isRestOpChar ||]
  , _lineComment       = "--"
  , _blockCommentStart = "{-"
  , _blockCommentEnd   = "-}"
  , _symbols           = symbols
  }

isFirstIdentChar :: Char -> Bool
isFirstIdentChar c = isLetter c

isRestIdentChar :: Char -> Bool
isRestIdentChar c = isAlphaNum c || c == '\''

isFirstOpChar :: Char -> Bool
isFirstOpChar c = case generalCategory c of
  MathSymbol           -> True
  CurrencySymbol       -> True
  ModifierSymbol       -> True
  OtherSymbol          -> True
  DashPunctuation      -> True
  ConnectorPunctuation -> True
  OpenPunctuation      -> case c of '(' -> False
                                    '{' -> False
                                    '.' -> False
                                    _   -> True
  ClosePunctuation     -> case c of ')' -> False
                                    '}' -> False
                                    _   -> True
  OtherPunctuation     -> case c of '\'' -> False
                                    '"'  -> False
                                    ';'  -> False
                                    _    -> True
  InitialQuote         -> True
  FinalQuote           -> True
  _                    -> False

isRestOpChar :: Char -> Bool
isRestOpChar c = isFirstOpChar c || isAlphaNum c || c == '\''

-- operator forms of lift, quote, splice might be stdlib-defined
symbols :: [String]
symbols = [
    "MetaTy"
  , "Ty"
  , "CompTy"
  , "ValTy"
  , "ElVal"
  , "ElComp"
  , "Prop"
  , "↑"
  , "^"
  , "="
  , ":="
  , "let"
  , "("
  , ")"
  , "{"
  , "}"
  , "<"
  , ">"
  , "Rec"
  , "."
  , ";"
  , "record"
  , "data"
  ]
