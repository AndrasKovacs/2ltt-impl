
module Parser.Parser (tm, top) where

import Prelude hiding (pi)
import Common hiding (some, many)
import qualified FlatParse.Stateful as FP
import Parser.Lexer
import Presyntax
import qualified Presyntax as Pre

{-
TODO
- Operator binders
- Grouped binders
- ML-style definitions
- Fixing sloppy positions.
- Records.
- Top level.
-}

many :: Parser a -> Parser (List a)
many p = FP.chainr Cons p (pure Nil)
{-# inline many #-}

some :: Parser a -> Parser (List a)
some p = do
  a <- p
  as <- many p
  pure $ Cons a as
{-# inline some #-}

anyLvlBase' :: Parser (Lvl, FP.Span)
anyLvlBase' = do
  FP.withSpan FP.anyAsciiDecimalWord \n s -> do
  let n' = fromIntegral n
  ws
  pure (n' , s)

anyLvl' :: Parser (Lvl, FP.Span)
anyLvl' = lvl *> anyLvlBase'

-- anyLvl :: Parser (Lvl, FP.Span)
-- anyLvl = (lvl' *> anyLvlBase') `cut` ["positive integer"]

arr :: Parser FP.Span
arr = $(switch [| case _ of "->" -> pure; "→" -> pure |])

arr' :: Parser FP.Span
arr' = $(switch' [| case _ of "->" -> pure; "→" -> pure |])

-- parl    = $(sym "(")
-- parl'   = $(sym' "(")
parr    = $(sym ")")
-- parr'   = $(sym' ")")
-- bracel  = $(sym "{")
bracel' = $(sym' "{")
bracer  = $(sym "}")
-- bracer' = $(sym' "}")
dot     = $(sym ".")
dot'    = $(sym' ".")
angler  = $(sym ">")
-- angler' = $(sym' ">")
-- tilde   = $(sym "~")
tilde'  = $(sym' "~")
-- colon   = $(sym ":")
colon'  = $(sym' ":")
semi    = $(sym' ";")
-- semi'   = $(sym  ";")

--------------------------------------------------------------------------------

atom' :: Parser Tm
atom' = $(switch' [| case _ of
  "("      -> \(FP.Span l r) -> do {t <- tm; r <- rightPos <$> parr; pure $ Parens l t r}
  "<"      -> \(FP.Span l r) -> do {t <- tm; r <- rightPos <$> angler; pure $ Quote l t r}
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
  |])
  <|> (Ident <$> ident')

atom :: Parser Tm
atom = do
  atom' `cut` ["atomic expression"]

projections :: Tm -> Parser Tm
projections = go where
  go t = FP.withOption dot'

    (\s -> ((do (n, s') <- anyLvl'
                go (Dot t (PLvl (leftPos s) n (rightPos s'))))
        <|> (do x <- ident'
                go (Dot t (PName x)))
        <|> (do x <- operator'
                pure (Dot t (POp x))))
        `cut` ["an identifier, operator chunk or a positive integer"]
    )
    (pure t)

projection' :: Parser Tm
projection' = projections =<< atom'

projection :: Parser Tm
projection = do
  x <- atom
  projections x

splice' :: Parser Tm
splice' = FP.withOption tilde'
  (\s -> Splice (leftPos s) <$> projection)
  projection'

splice :: Parser Tm
splice = FP.withOption tilde'
  (\s -> Splice (leftPos s) <$> projection')
  projection

spineEntry' :: Parser SpineEntry
spineEntry' =
      (do t <- splice'
          case t of Dot t (POp x) -> pure $ SEProjOp t x
                    t             -> pure $ SETm t)
  <|> (SEOp <$> operator')

spineEntry :: Parser SpineEntry
spineEntry =
      (do t <- splice
          case t of Dot t (POp x) -> pure $ SEProjOp t x
                    t             -> pure $ SETm t)
  <|> (SEOp <$> operator)

implicit :: Parser a -> Parser (a, Pre.Icit)
implicit p = FP.withOption bracel'
  (\(FP.Span l r) -> do {a <- p; bracer; pure (a, Pre.Impl l r)})
  (do {a <- p; pure (a, Pre.Expl)})

consSpine :: (SpineEntry, Pre.Icit) -> (Spine, Bool) -> (Spine, Bool)
consSpine (t, !i) (!sp, !isParsed) = case t of
  SETm{}     -> (SCons t i sp, isParsed)
  SEOp{}     -> (SCons t i sp, False)
  SEProjOp{} -> (SCons t i sp, False)

spine0 :: Parser (Spine, Bool)
spine0 =
  FP.withOption (implicit spineEntry')
    (\x -> consSpine x <$> spine0)
    (pure (SNil, True))

spine :: Parser Tm
spine = do
  hd <- spineEntry
  (sp, isParsed) <- spine0
  case (hd, sp, isParsed) of
    (SETm t, SNil, True) -> pure t
    (SETm t, sp  , True) -> pure $ Spine t sp
    _                    -> pure $ Unparsed hd sp

bind :: Parser Bind
bind = BName <$> ident

bind' :: Parser Bind
bind' = BName <$> ident'

multiBindBase :: Parser MultiBind
multiBindBase =
  $(switch' [| case _ of
    "{" -> \(FP.Span l _) -> do
      x <- bind
      a <- FP.optional (colon' *> tm)
      r <- rightPos <$> bracer
      pure $ MultiBind (Cons x Nil) (Pre.Impl l r) a
    "(" -> \(FP.Span l _) -> do
      x <- bind
      a <- FP.optional (colon' *> tm)
      r <- rightPos <$> parr
      pure $ MultiBind (Cons x Nil) Pre.Expl a|])

pi :: Parser Tm
pi = do
  l <- FP.getPos
  FP.withOption (some multiBindBase)
    (\binders -> do
        arr `cut` ["\"->\" or \"→\""]
        t <- pi
        pure $ Pi l binders t
    )
    (do a <- spine
        FP.branch arr'
         (do b <- pi
             -- TODO: the BUnused contains an incorrect position
             pure $ Pi l (Single (MultiBind (Single (BUnused l)) Pre.Expl (Just a))) b)
         (pure a)
    )

plainLamBind' :: Parser MultiBind
plainLamBind' = do
  x <- bind'
  pure $ MultiBind (Cons x Nil) Pre.Expl Nothing

lamBind' :: Parser MultiBind
lamBind' = multiBindBase <|> plainLamBind'

lamBody :: Pos -> Parser Tm
lamBody l = do
  x <- some lamBind' `cut` ["binder"]
  dot
  t <- tm
  pure $ Lam l x t
{-# noinline lamBody #-}

assign :: Parser Stage
assign = $(switch [| case _ of
  "="  -> \_ -> pure S1
  ":=" -> \_ -> pure S0
  |]) `cut` ["\"=\" or \":=\""]

letBody :: Pos -> Parser Tm
letBody l = do
  x <- bind
  a <- FP.optional (colon' *> tm)
  s <- assign
  t <- tm
  semi
  u <- tm
  pure $ Let l s x a t u
{-# noinline letBody #-}

tm :: Parser Tm
tm = $(switch [| case _ of
  "\\"  -> \(FP.Span l _) -> lamBody l
  "λ"   -> \(FP.Span l _) -> lamBody l
  "let" -> \(FP.Span l _) -> letBody l
  |])
  <|>
  pi

topEntry :: () -> Parser Top
topEntry _ = do
  x <- exactLvl' 0 *> bind'
  localIndentation 1 do
  l <- FP.ask
  a <- FP.optional (colon' *> tm)
  s <- assign
  t <- tm
  u <- localIndentation 0 $ top ()
  pure $ TDef s x a t u

topEof :: Parser Top
topEof =
  TNil <$ FP.eof
  `cut` ["end of file", "top-level definition or declaration at column 1"]

top :: () -> Parser Top
top _ = do
  topEntry () <|> topEof







--------------------------------------------------------------------------------
