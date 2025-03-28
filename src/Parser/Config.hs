
module Parser.Config (config) where

import qualified FlatParse.Stateful as FP
import Data.Char
import Parser.Batteries

isOperatorChar :: Char -> Bool
isOperatorChar c = case generalCategory c of
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
  , "Prf"
  , "Code"
  , "↑"
  , "="
  , ":="
  , "let"
  , "("
  , ")"
  ]

config :: Config
config = Config {
    _firstIdentChar    = [|| FP.satisfy isLetter ||]
  , _restIdentChar     = [|| FP.satisfy (\c -> c == '\'' || isAlphaNum c) ||]
  , _operatorChar      = [|| FP.satisfy isOperatorChar ||]
  , _whitespaceChars   = " \t\r\v\f"
  , _lineComment       = "--"
  , _blockCommentStart = "{-"
  , _blockCommentEnd   = "-}"
  , _symbols           = symbols
  }
