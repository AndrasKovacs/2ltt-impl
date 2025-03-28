
module Parser.Parser where

import Common
import qualified FlatParse.Stateful as FP
import Parser.Lexer
import Presyntax

atom :: Parser Tm
atom = $(switch [| case _ of
  "("      -> \(FP.Span l r) -> Parens l <$> tm' <*> (rightPos <$> $(sym ")"))
  "MetaTy" -> \(FP.Span l r) -> pure $ MetaTy l r
  "Ty"     -> \(FP.Span l r) -> pure $ Ty l r
  "CompTy" -> \(FP.Span l r) -> pure $ CompTy l r
  "ValTy"  -> \(FP.Span l r) -> pure $ ValTy l r
  |])



tm' :: Parser Tm
tm' = uf
