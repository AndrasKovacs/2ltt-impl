
module Parser.Parser where

import Common
import qualified FlatParse.Stateful as FP
import Parser.Lexer
import Presyntax

-- TODO: record terms

atom :: Parser Tm
atom = $(switch [| case _ of
  "("      -> \(FP.Span l r) -> Parens l <$> tm' <*> (rightPos <$> $(sym ")"))
  "<"      -> \(FP.Span l r) -> Quote l  <$> tm' <*> (rightPos <$> $(sym ">"))
  "MetaTy" -> \(FP.Span l r) -> pure $ MetaTy l r
  "Ty"     -> \(FP.Span l r) -> pure $ Ty l r
  "CompTy" -> \(FP.Span l r) -> pure $ CompTy l r
  "ValTy"  -> \(FP.Span l r) -> pure $ ValTy l r
  "ElVal"  -> \(FP.Span l r) -> pure $ ElVal l r
  "ElComp" -> \(FP.Span l r) -> pure $ ElComp l r
  "Prop"   -> \(FP.Span l r) -> pure $ Prop l r
  "_"      -> \(FP.Span l r) -> pure $ Inferred l
  "?"      -> \(FP.Span l r) -> pure $ Hole l
  "↑"      -> \(FP.Span l r) -> pure $ Lift l r
  "^"      -> \(FP.Span l r) -> pure $ Lift l r
  _        -> Ident <$> ident
  |])

tm' :: Parser Tm
tm' = uf
