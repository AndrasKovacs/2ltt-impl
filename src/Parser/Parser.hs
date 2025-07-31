
module Parser.Parser where

import Common
import qualified FlatParse.Stateful as FP
import Parser.Lexer
import Presyntax

anyLvlBase :: Parser (Lvl, FP.Span)
anyLvlBase = do
  FP.withSpan FP.anyWord \n s -> do
  let n' = fromIntegral n
  ws
  pure (n' , s)

anyLvl :: Parser (Lvl, FP.Span)
anyLvl = lvl *> anyLvlBase

anyLvl' :: Parser (Lvl, FP.Span)
anyLvl' = (lvl' *> anyLvlBase) `cut` ["positive integer"]

--------------------------------------------------------------------------------

atom :: Parser Tm
atom = $(switch [| case _ of
  "("      -> \(FP.Span l r) -> Parens l <$> tm' <*> (rightPos <$> $(sym ")"))
  "<"      -> \(FP.Span l r) -> Quote l  <$> tm' <*> (rightPos <$> $(sym ">"))
  "Set"    -> \(FP.Span l r) -> pure $ Set l r
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
  "@"      -> \(FP.Span l _) -> do {(n,rightPos -> r) <- anyLvl'; pure $ LocalLvl l n r}
  _        -> Ident <$> ident
  |])

atom' :: Parser Tm
atom' = atom `cut` ["atomic expression"]

-- projected operator should be handled!!
projections' :: Parser Tm
projections' = go =<< atom' where
  go :: Tm -> Parser Tm
  go t = FP.withOption $(sym ".")
    (\s ->      do {(n, s') <- anyLvl; go (Dot t (PLvl (leftPos s) n (rightPos s')))}
           <|>  uf
    )
    uf


-- splice :: Parser Tm
-- splice = FP.withOption $(sym "~")
--   (\s -> Splice (leftPos s) <$> projections)
--   projections

tm' :: Parser Tm
tm' = uf
