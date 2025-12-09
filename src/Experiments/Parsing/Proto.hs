
{-
Parser where operators produce an "error value" for unparsed spines.
-}

module Experiments.Parsing.Proto where

import Common hiding (name)
import Parser.Lexer
import qualified FlatParse.Stateful as FP

data Tm
  = Lam Name Tm
  | Let Name Tm Tm
  | Unparsed Spine
  | Spine Tm Spine
  | Var Name
  | Parens Tm
  deriving Show

data Spine
  = SNil
  | SApp Tm Spine
  | SOp Name Spine
  deriving Show

name :: Parser Name
name = NSpan <$> ident

op :: Parser Name
op = NSpan <$> operator

plet = $(sym "let")
psc  = $(sym ";")
peq  = $(sym "=")
pdot = $(sym ".")
pparl = $(sym "(")
pparr = $(sym ")")
plam  = $(sym "λ")

atom :: Parser Tm
atom = (Var <$> name)
   <|> (Parens <$> (pparl *> tm <* pparr))

spine'' :: Parser (Spine, Bool)
spine'' =
      do {x <- atom; (s, b) <- spine'; pure (SApp x s, b)}
  <|> do {x <- op;   (s, b) <- spine'; pure (SOp x s, True)}

spine' :: Parser (Spine, Bool)
spine' =
      do {x <- atom; (s, b) <- spine'; pure (SApp x s, b)}
  <|> do {x <- op;   (s, b) <- spine'; pure (SOp x s, True)}
  <|> pure (SNil, False)

spine :: Parser Tm
spine = spine'' >>= \case
  (s, True)            -> pure $ Unparsed s
  (SApp t SNil, False) -> pure t
  (SApp t s, False)    -> pure $ Spine t s
  _                    -> impossible

tm :: Parser Tm
tm = $(switch [| case _ of
  "let" -> \_ -> do {plet; x <- name; peq; t <- tm; psc; u <- tm; pure $ Let x t u}
  "λ"   -> \_ -> do {x <- name; pdot; t <- tm; pure $ Lam x t}
  _     -> spine
  |])

top :: Parser Tm
top = ws *> tm <* FP.eof

--------------------------------------------------------------------------------
