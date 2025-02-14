{-# options_ghc -Wno-unused-imports #-}

module Parser.Batteries where

import Common

import qualified Data.ByteString as B
import qualified Data.Set as S
import Language.Haskell.TH        hiding (Overlap)
import Language.Haskell.TH.Syntax hiding (Overlap(..))

import qualified FlatParse.Stateful as FP
import qualified FlatParse.Common.Switch as FP

type Parser = FP.Parser Int Error

data Expected
  = Lit String       -- ^ Name of expected thing.
  | ExactIndent Int  -- ^ Exact indentation level.
  | IndentMore Int   -- ^ More than given indentation level.
  deriving (Eq, Show, Ord)

data Error = Error FP.Pos [Expected] | DontUnbox
  deriving Show

errorPos :: Error -> FP.Pos
errorPos = \case
  Error p _ -> p
  _         -> undefined

-- | Merge two errors. Inner errors (which were thrown at points with more consumed inputs)
--   are preferred. If errors are thrown at identical input positions, we prefer precise errors
--   to imprecise ones.
--
--   The point of prioritizing inner and precise errors is to suppress the deluge of "expected"
--   items, and instead try to point to a concrete issue to fix.
mergeErrors :: Error -> Error -> Error
mergeErrors e@(Error p es) e'@(Error p' es')
  | p < p'     = e'
  | p > p'     = e
  | [_] <- es  = e
  | [_] <- es' = e'
  | otherwise  = Error p (es ++ es')
mergeErrors _ _ = undefined
{-# noinline mergeErrors #-} -- cold code

-- | Pretty print an error. The `B.ByteString` input is the source file. The offending line from the
--   source is displayed in the output.
prettyError :: B.ByteString -> Error -> String
prettyError b (Error pos es) =

  let ls     = FP.linesUtf8 b
      (l, c) = case FP.posLineCols b [pos] of x:_ -> x; _ -> undefined
      line   = if l < length ls then ls !! l else ""
      linum  = show l
      lpad   = map (const ' ') linum

      expected (Lit s)           = s
      expected (ExactIndent col) = "expected a token indented to column " ++ show (col + 1)
      expected (IndentMore col)  = "expected a token indented to column " ++ show (col + 1) ++ " or more."

      expecteds :: [Expected] -> String
      expecteds []     = error "impossible"
      expecteds [e]    = expected e
      expecteds (e:es) = expected e ++ go es where
        go []     = ""
        go [e]    = " or " ++ expected e
        go (e:es) = ", " ++ expected e ++ go es

  in show l ++ ":" ++ show c ++ ":\n" ++
     lpad   ++ "|\n" ++
     linum  ++ "| " ++ line ++ "\n" ++
     lpad   ++ "| " ++ replicate c ' ' ++ "^\n" ++
     "parse error: expected " ++ expecteds (S.toList $ S.fromList es)
prettyError _ _ = undefined

getPos :: Parser FP.Pos
getPos = FP.getPos
{-# inline getPos #-}

err :: [Expected] -> Parser a
err es = do
  p <- FP.getPos
  FP.err (Error p es)
{-# inline err #-}

cut :: Parser a -> [Expected] -> Parser a
cut p exps = do
  pos <- getPos
  FP.cutting p (Error pos exps) mergeErrors
{-# inline cut #-}

runParser :: Parser a -> B.ByteString -> FP.Result Error a
runParser p src = FP.runParser p 0 0 src

-- | Run parser, print pretty error on failure.
testParser :: Show a => Parser a -> String -> IO ()
testParser p (FP.strToUtf8 -> str) = case runParser p str of
    FP.Err e    -> putStrLn $ prettyError str e
    FP.OK a _ _ -> print a
    FP.Fail     -> putStrLn "parse error"

-- | Query the current indentation level, fail if it's smaller than the current expected level.
lvl :: Parser Int
lvl = do
  lvl <- FP.ask
  currentLvl <- FP.get
  if currentLvl < lvl
    then FP.empty
    else pure currentLvl
{-# inline lvl #-}

-- | Same as `lvl` except we throw an error on mismatch.
lvl' :: Parser Int
lvl' = do
  lvl <- FP.ask
  currentLvl <- FP.get
  if currentLvl < lvl
    then err [IndentMore lvl]
    else pure currentLvl
{-# inline lvl' #-}

-- | Fail if the current level is not the expected one.
exactLvl :: Int -> Parser ()
exactLvl l = do
  l' <- FP.get
  if l == l' then pure () else FP.empty
{-# inline exactLvl #-}

-- | Throw error if the current level is not the expected one.
exactLvl' :: Int -> Parser ()
exactLvl' l = do
  l' <- FP.get
  if l == l' then pure () else err [ExactIndent l]
{-# inline exactLvl' #-}

-- | Parse something, then run an action with token indentation level greater
--   then the level of the firstly parsed thing.
moreIndented :: Parser a -> (a -> Parser b) -> Parser b
moreIndented pa k = do
  lvl <- FP.get
  a <- pa
  FP.local (\_ -> lvl + 1) (k a)
{-# inline moreIndented #-}

-- | Run a parser with expected indentation level.
localIndentation :: Int -> Parser a -> Parser a
localIndentation n p = FP.local (\_ -> n) p
{-# inline localIndentation #-}


-- Template Haskell for generating basic parsing utilities
--------------------------------------------------------------------------------

-- | Lexer configuration.
--   - An identifier starts with a FirstIdentChar and is followed by 0 or more RestIdentChar-s, which is not
--     a reserved symbol
--   - An operator is a sequence of 1 or more OperatorChar-s which is not a reserved symbol.
--   - ASSUMPTION 1: operators and identifiers don't overlap.
--   - ASSUMPTION 2: symbols don't contain whitespace characters.
--   - A symbol is any nonempty sequence of non-whitespace characters.

data Config = Config {
    _firstIdentChar    :: (CodeQ (Parser Char))  -- ^ Parsing first character of an identifier.
  , _restIdentChar     :: (CodeQ (Parser Char))  -- ^ Parsing non-first characters of an identifier.
  , _operatorChar      :: (CodeQ (Parser Char))  -- ^ Parsing operator characters.
  , _whitespaceChars   :: String   -- ^ List of whitespace characters, excluding newline (which is always whitespace).
  , _lineComment       :: String   -- ^ Line comment start.
  , _blockCommentStart :: String   -- ^ Block comment start.
  , _blockCommentEnd   :: String   -- ^ Block comment end.
  , _symbols           :: [String] -- ^ List of reserved symbols (may overlap with idents and operators)
  }

data Overlap = IdentOverlap | OpOverlap | NoOverlap

-- Working around nested quote limitations
--------------------------------------------------------------------------------

handleOverlap :: Overlap -> Q Exp
handleOverlap = \case
  IdentOverlap -> [| FP.fails identChar    |]
  OpOverlap    -> [| FP.fails operatorChar |]
  NoOverlap    -> [| pure ()               |]

symBody :: S.Set String -> (String -> Overlap) -> Bool -> String -> Q Exp
symBody symbols overlap cut s | S.notMember s symbols =
  error $ "string " ++ show s ++ " is not among the reserved symbols: "
          ++ show (S.toList symbols)
symBody symbols overlap cut s =
  let p = [| spanOfToken $(FP.string s) <* FP.fails (operatorChar)|] in --  <* $(handleOverlap (overlap s))|] in
  if cut then [| $(p) `FP.cut` [Lit (Show s)] |] else p

switchBody :: (String -> Overlap) -> ([(String, Exp)], Maybe Exp) -> Q Exp
switchBody overlap (cases, deflt) =
      [| do lvl
            left <- FP.getPos
            $(FP.switch (FP.makeRawSwitch
                (map (\(s, body) ->
                   (s, [| do {$(handleOverlap (overlap s)); right <- FP.getPos; ws; $(pure body) (FP.Span left right)} |]))
                 cases)
                ((\deflt -> [| do {right <- FP.getPos; ws ; $(pure deflt)} |]) <$> deflt)))
        |]

--------------------------------------------------------------------------------

chargeBatteries :: Config -> DecsQ
chargeBatteries (Config identStart identRest opChar wsChars lineComment
                        blockCommentStart blockCommentEnd symbols) = do

  let
      blockCommentStartLen = length blockCommentStart
      blockCommentEndLen   = length blockCommentEnd
      lineCommentLen       = length lineComment

  [d|
    goLineComment :: Parser ()
    goLineComment =
      FP.withOption FP.anyWord8
        (\case 10 -> FP.put 0 >> ws
               _  -> FP.modify (+1) >> goLineComment)
        (pure ())

    blockComment :: Parser ()
    blockComment = go (1 :: Int) where
      go 0 = ws
      go n = $(FP.switch $ FP.makeRawSwitch [
          ("\n"              , [| FP.put 0 >> go n |])
        , (blockCommentStart , [| FP.modify (+ $(lift blockCommentStartLen)) >> go (n - 1) |])
        , (blockCommentEnd   , [| FP.modify (+ $(lift blockCommentEndLen))   >> go (n + 1) |]) ]
       (Just [| FP.branch FP.anyChar (FP.modify (+1) >> go n) (pure ()) |]))

    ws :: Parser ()
    ws = $(FP.switch $ FP.makeRawSwitch
      (
        ("\n",              [| FP.put 0 >> ws |])
      : (blockCommentStart, [| FP.modify (+ $(lift blockCommentStartLen)) >> blockComment |])
      : (lineComment,       [| FP.modify (+ $(lift lineCommentLen))       >> goLineComment |])
      : map (\c -> ([c], [| FP.modify (+1) >> ws |])) wsChars
      )
      (Just [| pure () |]))

    token :: Parser a -> Parser a
    token p = Parser.Batteries.lvl *> p <* ws
    {-# inline token #-}

    token' :: Parser a -> Parser a
    token' p = Parser.Batteries.lvl' *> p <* ws
    {-# inline token' #-}

    spanOfToken :: Parser a -> Parser FP.Span
    spanOfToken p = lvl *> FP.spanOf p <* ws
    {-# inline spanOfToken #-}

    spanOfToken' :: Parser a -> Parser FP.Span
    spanOfToken' p = lvl' *> FP.spanOf p <* ws
    {-# inline spanOfToken' #-}

    anySymbol :: Parser ()
    anySymbol = $(case symbols of
      [] -> [|FP.empty|]
      _  -> FP.switch $
              FP.makeRawSwitch
                (map (\s -> (s, [| FP.eof |])) (symbols))
                Nothing)

    ------------------------------------------------------------

    identStartChar :: Parser Char
    identStartChar = $(unTypeCode identStart)

    identChar :: Parser Char
    identChar = $(unTypeCode identRest)

    inlineIdentChar :: Parser Char
    inlineIdentChar = $(unTypeCode identRest)
    {-# inline inlineIdentChar #-}

    scanIdent :: Parser ()
    scanIdent = identStartChar >> FP.skipMany inlineIdentChar

    identBase :: Parser FP.Span
    identBase = FP.withSpan scanIdent \_ span -> do
      FP.fails $ FP.inSpan span anySymbol
      ws
      pure span

    -- | Parse an identifier.
    ident :: Parser FP.Span
    ident = lvl >> identBase
    {-# inline ident #-}

    -- | Parse an identifier.
    ident' :: Parser FP.Span
    ident' = lvl' >> identBase `cut` [Lit "identifier"]
    {-# inline ident' #-}

    ------------------------------------------------------------

    operatorChar :: Parser Char
    operatorChar = $(unTypeCode opChar)

    inlineOperatorChar :: Parser Char
    inlineOperatorChar = $(unTypeCode identRest)
    {-# inline inlineOperatorChar #-}

    scanOperator :: Parser ()
    scanOperator = FP.skipSome inlineOperatorChar

    operatorBase :: Parser FP.Span
    operatorBase = FP.withSpan scanOperator \_ span -> do
      FP.fails $ FP.inSpan span anySymbol
      ws
      pure span

    -- | Parse an identifier.
    operator :: Parser FP.Span
    operator = lvl >> operatorBase
    {-# inline operator #-}

    -- | Parse an identifier.
    operator' :: Parser FP.Span
    operator' = lvl' >> operatorBase `cut` [Lit "operator"]
    {-# inline operator' #-}

    ------------------------------------------------------------

    symbolSet :: S.Set String
    symbolSet = S.fromList symbols

    checkOverlap :: String -> Overlap
    checkOverlap s
      | FP.OK{} <- runParser (ws >> scanOperator >> FP.eof) (FP.strToUtf8 s) = OpOverlap
      | FP.OK{} <- runParser (ws >> scanIdent    >> FP.eof) (FP.strToUtf8 s) = IdentOverlap
      | True = NoOverlap

    -- | Parse a symbol
    sym :: String -> Q Exp
    sym s = symBody symbolSet checkOverlap False s

    sym' :: String -> Q Exp
    sym' s = symBody symbolSet checkOverlap True s

    switch :: Q Exp -> Q Exp
    switch cases = switchBody checkOverlap =<< FP.parseSwitch cases
    |]
