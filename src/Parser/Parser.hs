
module Parser.Parser where

import Common
import qualified FlatParse.Stateful as FP
import Parser.Lexer
import Presyntax

atom :: Parser Tm
atom = $(switch [| case _ of
  "("      -> \(FP.Span l r) -> Parens l <$> tm' <*> (rightPos <$> $(sym ")"))
  "<"      -> \(FP.Span l r) -> Quote l <$> tm' <*> (rightPos <$> $(sym ">"))
  "Rec"    -> \(FP.Span l r) -> _
  "MetaTy" -> \(FP.Span l r) -> pure $ MetaTy l r
  "Ty"     -> \(FP.Span l r) -> pure $ Ty l r
  "CompTy" -> \(FP.Span l r) -> pure $ CompTy l r
  "ValTy"  -> \(FP.Span l r) -> pure $ ValTy l r
  "ElVal"  -> \(FP.Span l r) -> pure $ ElVal l r
  "ElComp" -> \(FP.Span l r) -> pure $ ElComp l r
  "Prop"   -> \(FP.Span l r) -> pure $ Prop l r
  "Prf"    -> \(FP.Span l r) -> pure $ Prf l r
  "_"      -> \(FP.Span l r) -> pure $ Inferred l
  "?"      -> \(FP.Span l r) -> pure $ Hole l
  "↑"      -> \(FP.Span l r) -> pure $ Lift l r
  "^"      -> \(FP.Span l r) -> pure $ Lift l r
  _        -> Ident <$> ident
  |])

atom' :: Parser Tm
atom' = atom `cut` [Lit "atomic expression"]


-- question: where to inject custom operators?
-- f ((x : A) -> B)
-- f let x = k; b
-- f λ x. a b c d

-- λ can bind stronger than any user op
-- let can also
-- Π can be weaker than any user op


tm' :: Parser Tm
tm' = uf
