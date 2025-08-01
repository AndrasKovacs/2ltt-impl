
module Parser.Batteries where

-- import Debug.Trace

import Data.String
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
  | IndentMore Int Int  -- ^ More than given indentation level.
  deriving (Eq, Show, Ord)

instance IsString Expected where
  fromString = Lit

data Error = Error FP.Pos [Expected] | DontUnbox
  deriving Show

errorPos :: Error -> FP.Pos
errorPos = \case
  Error p _ -> p
  _         -> undefined

-- | Merge two errors. Errors which were thrown at points with more consumed inputs are
--   preferred. If errors are thrown at identical input positions, we prefer precise errors to
--   imprecise ones, and later thrown errors to earlier thrown ones.
--
-- This is to suppress the deluge of "expected" items, and instead try to point to a concrete issue
-- to fix.
mergeErrors :: Error -> Error -> Error
mergeErrors e@(Error p es) e'@(Error p' es') = case compare p p' of
  LT -> e'
  GT -> e
  EQ -> case (es, es') of
    ([_], [_]) -> e'
    ([_], _  ) -> e
    (_  , [_]) -> e'
    _          -> Error p (es ++ es')
mergeErrors _ _ = undefined
{-# noinline mergeErrors #-} -- cold code

-- | Pretty print an error. The `B.ByteString` input is the source file. The offending line from the
--   source is displayed in the output.
prettyError :: B.ByteString -> Error -> String
prettyError b (Error pos es) =

  let ls     = FP.linesUtf8 b
      (l, c) = case FP.posLineCols b [pos] of x:_ -> x; _ -> undefined
      line   = if l < length ls then ls !! l else ""
      linum  = show (l + 1)
      lpad   = map (const ' ') linum

      expected (Lit s)           = s
      expected (ExactIndent col) = "expected a token indented to column " ++ show (col + 1)
      expected (IndentMore ex cur)  = "expected a token indented to column " ++ show (ex + 1) ++ " or more, "
                                       ++ "actually indented to column " ++ show (cur + 1)

      expecteds :: [Expected] -> String
      expecteds []     = error "impossible"
      expecteds [e]    = expected e
      expecteds (e:es) = expected e ++ go es where
        go []     = ""
        go [e]    = " or " ++ expected e
        go (e:es) = ", " ++ expected e ++ go es

  in linum ++ ":" ++ show (c + 1) ++ ":\n" ++
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
    FP.Err e       -> putStrLn $ prettyError str e
    FP.OK a _ rest -> do print a
                         print rest
    FP.Fail        -> putStrLn "parse failure"

-- | Query the current indentation level, fail if it's smaller than the current expected level.
lvl' :: Parser Int
lvl' = do
  lvl <- FP.ask
  currentLvl <- FP.get
  if currentLvl < lvl
    then FP.empty
    else pure currentLvl
{-# inline lvl' #-}

-- | Same as `lvl` except we throw an error on mismatch.
lvl :: Parser Int
lvl = do
  lvl <- FP.ask
  currentLvl <- FP.get
  if currentLvl < lvl
    then err [IndentMore lvl currentLvl]
    else pure currentLvl
{-# inline lvl #-}

-- | Fail if the current level is not the expected one.
exactLvl' :: Int -> Parser ()
exactLvl' l = do
  l' <- FP.get
  if l == l' then pure () else FP.empty
{-# inline exactLvl' #-}

-- | Throw error if the current level is not the expected one.
exactLvl :: Int -> Parser ()
exactLvl l = do
  l' <- FP.get
  if l == l' then pure () else err [ExactIndent l]
{-# inline exactLvl #-}

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

data Config = Config {
    _lexicalSwitch     :: Char     -- ^ Turns identifiers into operators an vice verse when
                                   --   used as a prefix.
  , _whitespaceChars   :: String   -- ^ List of whitespace characters, excluding newline (which is always whitespace).
  , _firstIdentChar    :: CodeQ (Parser Char) -- ^ Parsing first character of an identifier.
  , _restIdentChar     :: CodeQ (Parser Char) -- ^ Parsing non-first characters of an identifier.
  , _opChar            :: CodeQ (Parser Char) -- ^ Parsing first character of an operator chunk.
  , _lineComment       :: String   -- ^ Line comment start.
  , _blockCommentStart :: String   -- ^ Block comment start.
  , _blockCommentEnd   :: String   -- ^ Block comment end.
  , _symbols           :: [String] -- ^ List of reserved symbols (may overlap with identifiers and operators)
  }

data Overlap = IdentOverlap | OpOverlap | NoOverlap

-- Working around nested quote limitations
--------------------------------------------------------------------------------

handleOverlap :: Overlap -> Q Exp
handleOverlap = \case
  IdentOverlap -> [| FP.fails identRestChar |]
  OpOverlap    -> [| FP.fails opChar        |]
  NoOverlap    -> [| pure () |]

notReservedError :: S.Set String -> String -> a
notReservedError syms s =
  error $ "string " ++ show s ++ " is not among the reserved symbols: "
          ++ show (S.toList syms)

symBody :: S.Set String -> (String -> Overlap) -> Bool -> String -> Char -> Q Exp
symBody _ _ _ (c:cs) switch | c == switch =
  error $ "symbols cannot begin with the switch character"
symBody symbols overlap cut s switch | S.notMember s symbols =
  notReservedError symbols s
symBody symbols overlap cut s switch = let
  plvl   = if cut then [| Parser.Batteries.lvl  |]
                  else [| Parser.Batteries.lvl' |]
  pcut p = if cut then [| $p `Parser.Batteries.cut` [Lit (show @String s)] |]
                  else p
  base = [| FP.spanOf $(FP.string s)|]
  in pcut [| $plvl *> $base <* $(handleOverlap (overlap s)) <* ws |]

switchBody :: S.Set String -> (String -> Overlap) -> Bool -> ([(String, Exp)], Maybe Exp) -> Q Exp
switchBody symbols overlap cut (cases, deflt) =
      [| do $(if cut then [| lvl |] else [| lvl' |])
            left <- FP.getPos
            $(FP.switch (FP.makeRawSwitch
                (map (\(s, body) ->
                        if S.notMember s symbols then
                          notReservedError symbols s
                        else
                          (s, [| do {$(handleOverlap (overlap s));
                                     right <- FP.getPos;
                                     ws;
                                     $(pure body) (FP.Span left right)} |])
                     )
                 cases)
                ((\deflt -> [| do {right <- FP.getPos; ws ; $(pure deflt)} |]) <$> deflt)))
        |]

--------------------------------------------------------------------------------

chargeBatteries :: Config -> DecsQ
chargeBatteries (Config switchChar wsChars identStart identRest op lineComment
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

    identRestChar :: Parser Char
    identRestChar = $(unTypeCode identRest)

    inlineIdentRestChar :: Parser Char
    inlineIdentRestChar = $(unTypeCode identRest)
    {-# inline inlineIdentRestChar #-}

    scanIdent :: Parser ()
    scanIdent = identStartChar >> FP.skipMany inlineIdentRestChar

    identBase :: Parser FP.Span
    identBase = FP.withSpan scanIdent \_ span -> do
      FP.fails $ FP.inSpan span anySymbol
      ws
      pure span

    -- | Parse an identifier.
    ident' :: Parser FP.Span
    ident' = do
      lvl'
      FP.branch $(FP.char switchChar) operatorBase identBase
    {-# inline ident' #-}

    -- | Parse an identifier.
    ident :: Parser FP.Span
    ident = do
      lvl
      FP.branch $(FP.char switchChar) operatorBase identBase `cut` [Lit "identifier"]
    {-# inline ident #-}

    -- -- | Parse an identifier.
    -- identNoLvl :: Parser FP.Span
    -- identNoLvl =
    --   FP.branch $(FP.char switchChar) operatorBase identBase `cut` [Lit "identifier"]
    -- {-# inline identNoLvl #-}

    ------------------------------------------------------------

    opChar :: Parser Char
    opChar = $(unTypeCode op)

    inlineOpChar :: Parser Char
    inlineOpChar = $(unTypeCode op)
    {-# inline inlineOpChar #-}

    scanOperator :: Parser ()
    scanOperator = FP.skipSome inlineOpChar

    operatorBase :: Parser FP.Span
    operatorBase = FP.withSpan scanOperator \_ span -> do
      FP.fails $ FP.inSpan span anySymbol
      ws
      pure span

    -- | Parse an operator.
    operator' :: Parser FP.Span
    operator' = lvl' >> operatorBase
    {-# inline operator' #-}

    -- | Parse an operator.
    operator :: Parser FP.Span
    operator = lvl >> operatorBase `cut` [Lit "operator"]
    {-# inline operator #-}

    ------------------------------------------------------------

    symbolSet :: S.Set String
    symbolSet = S.fromList symbols

    checkOverlap :: String -> Overlap
    checkOverlap s
      | FP.OK{} <- runParser (scanOperator >> FP.eof) (FP.strToUtf8 s) = OpOverlap
      | FP.OK{} <- runParser (scanIdent    >> FP.eof) (FP.strToUtf8 s) = IdentOverlap
      | True = NoOverlap

    -- | Parse a symbol
    sym' :: String -> Q Exp
    sym' s = symBody symbolSet checkOverlap False s switchChar

    sym :: String -> Q Exp
    sym s = symBody symbolSet checkOverlap True s switchChar

    switch :: Q Exp -> Q Exp
    switch cases = switchBody symbolSet checkOverlap True =<< FP.parseSwitch cases

    switch' :: Q Exp -> Q Exp
    switch' cases = switchBody symbolSet checkOverlap False =<< FP.parseSwitch cases
    |]
