{-# options_ghc -Wno-unused-binds #-}

module Parser (tm, top) where

import Prelude hiding (pi)
import Common hiding (some, many, debug, Proj(..), Prim(..), name, Bind(..))
import FlatParse.Stateful qualified as FP
import Parser.Lexer
import Presyntax


{-
TODO
- Grouped binders
- ML-style definitions
- data types, case splits
- implicit let
- indentation-based let

- Andreas suggestion: lambda should be included in the operator parser, so
  that we can e.g. write  < \x. x >  where <_> is a closed operator.
-}

debug :: String -> Parser ()
debug msg = do
  l <- FP.traceLine
  traceM $ msg ++ " |" ++ l

many :: Parser a -> Parser (List a)
many p = FP.chainr Cons p (pure Nil)
{-# inline many #-}

some :: Parser a -> Parser (List a)
some p = do
  a <- p
  as <- many p
  pure $ Cons a as
{-# inline some #-}

anyWordBase' :: Parser (Word, FP.Span)
anyWordBase' = do
  FP.withSpan FP.anyAsciiDecimalWord \n s -> do
  ws
  pure (n , s)

anyWord' :: Parser (Word, FP.Span)
anyWord' = lvl' *> anyWordBase'

anyLvl' :: Parser (Lvl, FP.Span)
anyLvl' = coerce anyWord'

-- anyWord :: Parser (Word, FP.Span)
-- anyWord = (lvl' *> anyWordBase') `cut` ["positive integer"]

-- anyLvl :: Parser (Lvl, FP.Span)
-- anyLvl = coerce anyWord

arr :: Parser Span
arr = $(switch [| case _ of "->" -> pure; "→" -> pure |])

arr' :: Parser Span
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
colon   = $(sym ":")
colon'  = $(sym' ":")
semi    = $(sym' ";")
-- semi'   = $(sym  ";")

rawUnderscore = $(rawString "_")
rawLeft  = $(rawString "left")
rawRight = $(rawString "right")

--------------------------------------------------------------------------------

atom' :: Parser Tm
atom' = $(switch' [| case _ of
  "("      -> \(Span l r) -> do {t <- tm; r <- rightPos <$> parr; pure $ Parens l t r}
  "<"      -> \(Span l r) -> do {t <- tm; r <- rightPos <$> angler; pure $ Quote l t r}
  "Set"    -> \(Span l r) -> pure $ Set l r
  "Ty"     -> \(Span l r) -> pure $ Ty l r
  "CompTy" -> \(Span l r) -> pure $ CompTy l r
  "ValTy"  -> \(Span l r) -> pure $ ValTy l r
  "ElVal"  -> \(Span l r) -> pure $ ElVal l r
  "ElComp" -> \(Span l r) -> pure $ ElComp l r
  "_"      -> \(Span l r) -> pure $ Inferred l
  "?"      -> \(Span l r) -> pure $ Hole l
  "↑"      -> \(Span l r) -> pure $ Lift l r
  "^"      -> \(Span l r) -> pure $ Lift l r
  "@"      -> \(Span l _) -> do {(n,rightPos -> r) <- anyLvl'; pure $ LocalLvl l n r}
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

implicit :: Parser Tm -> Parser (Tm, Icit)
implicit p = FP.withOption bracel'
  (\(Span l r) -> do {a <- p; bracer; pure (Parens l a r, Impl)})
  (do {a <- p; pure (a, Expl)})

data SomeSpine where
  SomeSpine :: Sing b -> Spine b -> SomeSpine

-- TODO: trailing lambdas in spines
spTail :: Parser SomeSpine
spTail =
  FP.withOption operator'
    (\op -> do
        SomeSpine b sp <- spTail
        pure $ SomeSpine SFalse $ SOp op sp
    )
    (FP.withOption (implicit splice')
      (\(t, i) -> do
          SomeSpine b sp <- spTail
          case (t, i) of
            (Dot t (POp x), Expl) -> pure $ SomeSpine SFalse (SProjOp t x sp)
            (t, i) -> pure $ SomeSpine b (STm t i sp)
      )
      (pure $ SomeSpine STrue SNil)
    )

-- TODO: better errors
spine :: Parser Tm
spine = do
  FP.withOption operator'
    (\op -> do
        SomeSpine b sp <- spTail
        pure $ Unparsed $ USOp op sp
    )
    (do
      t <- splice
      SomeSpine b sp <- spTail
      case t of
        Dot t (POp x) -> pure $ Unparsed $ USProjOp t x sp
        t -> case b of
          STrue  -> case sp of
            SNil -> pure t
            sp   -> pure $ Spine t sp
          SFalse -> pure $ Unparsed $ USTm t sp
      )

prec :: Parser Precedence
prec = coerce . fst <$> (anyWord' `cut` ["precedence number"])

-- TODO: errors
bind' :: Parser Bind
bind' =
  FP.withOption ident'
    (\id -> pure $ BName id)
    (do
      lvl'
      FP.withOption rawUnderscore
        (\(Span l _) -> FP.withOption rawOperator
          (\op -> do
              ops <- many (rawUnderscore *> rawOperator)
              FP.withOption rawUnderscore
                (\_ -> do
                  ws <* lvl
                  fixity <- (rawLeft  *> ws *> (FInLeft <$> prec))
                        <|> (rawRight *> ws *> (FInLeft <$> prec))
                        <|> (FInNon <$> prec)
                  pure $ BOp $ Op fixity (Cons op ops)
                )
                (do
                  prec <- ws *> prec
                  pure $ BOp $ Op (FPost prec) (Cons op ops)
                )
          )
          (pure $ BUnused l)
        )
        (do op <- rawOperator
            rawUnderscore
            ops <- many (rawOperator <* rawUnderscore)
            FP.withOption rawOperator
              (\op' -> do
                ws
                pure $ BOp $ Op FClosed (Cons op ops <> Single op')
              )
              (do
                prec <- ws *> prec
                pure $ BOp $ Op (FPre prec) (Cons op ops)
              )
        )
    )

bind :: Parser Bind
bind = bind' `cut` ["binder"]


piBindBase :: Parser MultiBind
piBindBase =
  $(switch' [| case _ of
    "{" -> \(Span l _) -> do
      x <- bind
      a <- FP.optional (colon' *> tm)
      r <- rightPos <$> bracer
      pure $ MultiBind (Single x) Impl a
    "(" -> \(Span l _) -> do
      x <- bind'
      a <- colon' *> tm -- we only learn at this colon that we're parsing a binder
      r <- rightPos <$> parr
      pure $ MultiBind (Single x) Expl (Just a)|])

lamBind :: Parser MultiBind
lamBind =
  $(switch' [| case _ of
    "{" -> \(Span l _) -> do
      x <- bind
      a <- FP.optional (colon' *> tm)
      r <- rightPos <$> bracer
      pure $ MultiBind (Single x) Impl a
    "(" -> \(Span l _) -> do
      x <- bind
      a <- FP.optional (colon' *> tm)
      r <- rightPos <$> parr
      pure $ MultiBind (Single x) Expl a
    _ -> do
      x <- bind'
      pure $ MultiBind (Single x) Expl Nothing
    |])

pi :: Parser Tm
pi = do
  l <- getPos
  FP.withOption (some piBindBase)
    (\binders -> do
        arr `cut` ["\"->\" or \"→\""]
        t <- pi
        pure $ Pi l binders t
    )
    (do a <- spine
        FP.branch arr'
         (do b <- pi
             pure $ Pi l (Single (MultiBind (Single BNonExistent) Expl (Just a))) b)
         (pure a)
    )

lamBody :: Pos -> Parser Tm
lamBody l = do
  x <- some lamBind `cut` ["binder"]
  dot
  t <- tm
  pure $ Lam l x t
{-# noinline lamBody #-}

assign' :: Parser Stage
assign' = $(switch' [| case _ of
  "="  -> \_ -> pure S1
  ":=" -> \_ -> pure S0
  |])

letBody :: Pos -> Parser Tm
letBody l = do
  x <- bind
  a <- FP.optional (colon' *> tm)
  FP.withOption ((,) <$> assign' <*> tm)
    (\(s, t) -> do
        semi
        u <- tm
        pure $ Let l s x a t u
    )
    (case a of
       Just a -> do
         semi
         u <- tm
         pure $ Decl0 l x a u
       Nothing ->
         err ["=", ":="]
    )
{-# noinline letBody #-}

letrecBody :: Pos -> Parser Tm
letrecBody l = do
  x <- bind
  a <- FP.optional (colon' *> tm)
  $(sym ":=")
  t <- tm
  semi
  u <- tm
  pure $ LetRec l x a t u
{-# noinline letrecBody #-}

tm :: Parser Tm
tm = $(switch [| case _ of
  "\\"     -> \(Span l _) -> lamBody l
  "λ"      -> \(Span l _) -> lamBody l
  "let"    -> \(Span l _) -> letBody l
  "letrec" -> \(Span l _) -> letrecBody l
  |])
  <|>
  pi

{-# inline alignMany #-}
alignMany :: Show a => Show b => Parser a -> Parser b -> Parser (List (a, b))
alignMany pa pb = do
  lvl <- FP.get
  let aligned p      = exactLvl' lvl *> localIndentation lvl p
  let moreIndented p = localIndentation (lvl + 1) p
  FP.withOption pa
    (\a -> do
        b <- moreIndented pb
        Cons (a, b) <$> many ((,) <$> aligned pa <*> moreIndented pb)
    )
    (pure Nil)

topEntry :: () -> Parser Top
topEntry _ =
  -- records
  FP.withOption (exactLvl' 0 *> $(sym' "record"))
    (\(Span l _) -> localIndentation 1 do
       x <- bind
       params <- many piBindBase
       colon
       a <- tm
       $(sym "where")
       fields <- alignMany bind' (colon *> tm)
       u <- localIndentation 0 $ top' ()
       pure $ TRecord l x params a fields u
    )

    -- definitions and forward declarations
    (do
       x <- exactLvl' 0 *> bind'
       localIndentation 1 do
       a <- FP.optional (colon' *> tm)
       FP.withOption assign'
         (\s -> do
             t <- tm
             u <- localIndentation 0 $ top' ()
             pure $ TDef s x a t u
         )
         (case a of
            Just a -> do
              u <- localIndentation 0 $ top' ()
              pure $ TDecl x a u
            Nothing ->
              err ["=", ":="]
         )
    )

topEof :: Parser Top
topEof =
  TNil <$ FP.eof
  `cut` ["end of file", "top-level definition or declaration at column 1"]

top' :: () -> Parser Top
top' _ = topEntry () <|> topEof

top :: Parser Top
top = ws *> top' ()

p1 :: String
p1 =
  """
  -- record Foo (A : Set)(B : Set) : Set where
  --   field1 : Nat
  --   field2 : Nat

  -- record Pair (A : Ty)(B : Ty) : Ty where
  --   fst : A
  --   snd : B

  -- record Bar : Set where kuka : Nat
  --                        béka : Nat

  foo : (x : A)(y : A) -> mallac = Set



  -- Nat  : Set = (N : Set) → (N → N) → N → N
  -- zero : Nat = λ N s z. z
  -- suc  : Nat → Nat = λ n N s z. s (n N s z)
  -- _+_ left 10 : Nat → Nat → Nat = λ n m N s z. n N s (m N s z)
  -- n5 : Nat = suc (suc (suc (suc (suc zero))))
  -- n10 : Nat = n5 + n5
  """



--------------------------------------------------------------------------------
