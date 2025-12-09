
{-# options_ghc -Wno-unused-imports -Wno-orphans #-}

module Experiments.Parsing.Pratt where

import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Applicative
import Control.Monad
import Debug.Trace
import Data.String

-- Minimal
--------------------------------------------------------------------------------

-- type Op = String

-- data Exp = Lit Int | Add Exp Exp | Mul Exp Exp | Par Exp
--   deriving Show

-- type Parser a = StateT [Either Int Op] Maybe a

-- pop :: Parser (Either Int Op)
-- pop = get >>= \case
--   x:xs -> do put xs; pure x
--   _    -> empty

-- lit :: Parser Exp
-- lit = pop >>= \case
--   Left i -> pure $ Lit i
--   _      -> empty

-- op :: Op -> Parser ()
-- op str = pop >>= \case
--   Right str' | str == str' -> pure ()
--   _ -> empty

-- atom = lit <|> (op "(" *> add <* op ")")

-- mul  = do
--   t <- atom
--   (op "*" *> (Mul t <$> mul)) <|> pure t

-- add  = do
--   t <- mul
--   (op "+" *> (Add t <$> add)) <|> pure t

-- run :: Parser a -> [Either Int Op] -> Maybe (a, [Either Int Op])
-- run p s = runStateT p s


-- Transposing the recursive parser to get a Pratt parser
--------------------------------------------------------------------------------

-- type Op = String

-- data Exp = Lit Int | Op Op [Exp]
--   deriving Show

-- type Parser a = State [Either Int Op] a

-- instance IsString (Either a String) where
--   fromString = Right

-- instance Num (Either Int a) where
--   fromInteger = Left . fromIntegral
--   (+) = undefined; (*) = undefined; abs = undefined
--   signum = undefined; negate = undefined

-- peek :: Parser (Maybe (Either Int Op))
-- peek = get >>= \case
--   []   -> pure Nothing
--   x:xs -> pure (Just x)

-- pop :: Parser ()
-- pop = modify (drop 1)

-- op :: Op -> Parser ()
-- op str = peek >>= \case
--   Just (Right str') | str == str' -> pop
--   _ -> error $ "expected " ++ str

-- -- closed, prefix
-- go :: Int -> Parser Exp
-- go p = do
--   let ret = loop p Nothing
--   peek >>= \case
--     Just (Left i)    -> do pop; ret (Lit i)
--     Just (Right "(") -> do pop; t <- go 20; op ")"; ret (Op "(_)" [t])
--     Just (Right "!") -> do pop; t <- go 10; ret (Op "!" [t])
--     Just (Right "[") -> do {pop; t <- go 20; peek >>= \case
--       Just (Right "]1") -> ret (Op "[_]1" [t])
--       Just (Right "]2") -> ret (Op "[_]2" [t])
--       _                 -> error "expected ]1 or ]2"}
--     _ -> error "unexpected eof"

-- -- infix, postfix
-- -- the extra (Maybe Int) arg is purely to detect chained nonfix
-- loop :: Int -> Maybe Int -> Exp -> Parser Exp
-- loop p nonfix t =
--   peek >>= \case
--     Just (Right "+")
--       | p < 20 -> pure t
--       | True  -> do pop; u <- go 20; loop p Nothing (Op "_+_" [t, u])
--     Just (Right "*")
--       | p < 10 -> pure t
--       | True  -> do pop; u <- go 10; loop p Nothing (Op "_*_" [t, u])
--     Just (Right "++")
--       | p < 10 -> pure t
--       | True  -> do pop; loop p Nothing (Op "_++" [t])
--     Just (Right "==")
--       | p < 15            -> pure t
--       | nonfix == Just 15 -> error "can't chain =="
--       | True              -> do pop; u <- go 10; loop p (Just 15) (Op "_==_" [t, u])
--     Just (Right op) -> error $ "unknown operator: " ++ op
--     Just (Left i)   -> error $ "unexpected literal"
--     Nothing -> pure t

-- run :: Parser a -> [Either Int Op] -> (a, [Either Int Op])
-- run p s = runState p s
-- test s = run (go 20) s

--------------------------------------------------------------------------------

data Exp = Lit Int | Op Operator [Exp]
  deriving Show

type Parser a = State [Either Int String] a

instance IsString (Either a String) where
  fromString = Right

instance Num (Either Int a) where
  fromInteger = Left . fromIntegral
  (+) = undefined; (*) = undefined; abs = undefined
  signum = undefined; negate = undefined

peek :: Parser (Maybe (Either Int String))
peek = get >>= \case
  []   -> pure Nothing
  x:xs -> pure (Just x)

pop :: Parser ()
pop = modify (drop 1)

op :: String -> Parser ()
op str = peek >>= \case
  Just (Right str') | str == str' -> pop
  _ -> error $ "expected " ++ str

-- Prefix and closed operators
type LeftTable = Map String LeftNode
data LeftNode  = LNode (Set LFixity) LeftTable deriving Show

ltable (LNode _ t) = t

-- Infix and postfix operators
type InTable = Map String InNode
data InNode  = INode Int (Set IFixity) InTable deriving Show

itable (INode _ _ t) = t

data LFixity = LFClosed | LFPref Int deriving (Show, Eq, Ord)
data IFixity = IFLeft Int | IFRight Int | IFNon Int | IFPost Int deriving (Eq, Ord, Show)
data Fixity  = LF LFixity | IF IFixity deriving Show

prec :: IFixity -> Int
prec = \case
  IFLeft p  -> p
  IFRight p -> p
  IFNon p   -> p
  IFPost p  -> p

type Operator = ([String], Fixity) -- nonempty list
type Table = (LeftTable, InTable)

insert :: Operator -> Table -> Table
insert (ops, f) (lt, it) = case f of
  LF f -> (ltable (insertL ops f (LNode mempty lt)), it)
  IF f -> (lt, itable (insertI ops f (INode 0 mempty it)))

insertL :: [String] -> LFixity -> LeftNode -> LeftNode
insertL ops f (LNode fs t) = case ops of
  []     -> LNode (Set.insert f fs) t
  op:ops -> LNode fs $ Map.insertWith
    (\_ -> insertL ops f)
    op
    (insertL ops f (LNode mempty mempty))
    t

insertI :: [String] -> IFixity -> InNode -> InNode
insertI ops f (INode p fs t) = case ops of
  []     -> INode (max p (prec f)) (Set.insert f fs) t
  op:ops -> INode (max p (prec f)) fs $ Map.insertWith
    (\_ -> insertI ops f)
    op
    (insertI ops f (INode 0 mempty mempty))
    t

makeTable :: [Operator] -> Table
makeTable = foldl' (flip insert) (mempty, mempty)

dbg :: String -> Parser ()
dbg str = do
  s <- get
  traceM $ str ++ " | " ++ show s

parse :: Table -> Parser Exp
parse (ltbl, itbl) = left ltbl 0 [] [] where

  left :: LeftTable -> Int -> [Exp] -> [String] -> Parser Exp
  left tbl p sp acc = peek >>= \case

    Just (Left i) -> case sp of
      [] -> do pop; inside itbl p (Lit i) [] []
      _  -> error $ "unexpected literal: " ++ show i

    Just (Right op) -> case Map.lookup op tbl of
      Just (LNode fs tbl)

        -- "reset": apply operator to spine
        | [f] <- Set.toList fs, Map.null tbl -> do
            pop
            let theOp = reverse (op:acc)
            case f of
              LFClosed -> do
                let args = reverse sp
                inside itbl p (Op (theOp, LF f) args) [] []
              LFPref p' -> do
                t <- left ltbl p' [] []
                let args = reverse (t:sp)
                inside itbl p (Op (theOp, LF f) args) [] []

        -- "shift": parse another arg, push to stack
        | Set.null fs -> do
            pop
            t <- left ltbl 0 [] []
            left tbl p (t:sp) (op:acc)
        | True -> error "ambiguous grammar"

      Nothing -> error $ "unknown operator chunk: " ++ op
    Nothing -> error "unexpected eof"

  inside :: InTable -> Int -> Exp -> [Exp] -> [String] -> Parser Exp
  inside tbl p t sp acc = peek >>= \case

    Just (Left i) ->
      error $ "unexpected literal: " ++ show i

    Just (Right op) -> case Map.lookup op tbl of
      Just (INode maxp fs tbl)

        -- stop parsing if all possible operators are weaker than the current level
        | maxp < p -> case sp of
            [] -> pure t
            _  -> error "no backtracking allowed"

        -- "reset": apply operator to spine
        | [f] <- Set.toList fs, Map.null tbl -> do
            pop
            let theOp = reverse (op:acc)
            case f of
              IFLeft p' -> do
                u <- left ltbl (p' + 1) [] []
                let args = t:reverse (u:sp)
                inside itbl p (Op (theOp, IF f) args) [] []

              IFRight p' -> do
                u <- left ltbl p' [] []
                let args = t:reverse (u:sp)
                inside itbl p (Op (theOp, IF f) args) [] []

              IFNon p' ->
                error "TODO: non-associative op"

              IFPost p' -> do
                let args = reverse sp
                inside itbl p (Op (theOp, IF f) args) [] []

         -- "shift": push new arg to stack
         | Set.null fs -> do
             u <- left ltbl 0 [] []
             inside tbl p t (u:sp) (op:acc)

         | True ->
           error "ambiguous grammar"

      Nothing -> pure t
    Nothing -> pure t

--------------------------------------------------------------------------------

ops :: [Operator]
ops = [
    -- (["+"], IF $ IFRight 5)
 -- ,  (["!"], LF $ LFPref 4)
  -- , (["*"], IF $ IFRight 6)
  -- , (["(",")"], LF $ LFClosed)
    (["if", "then", "else"], LF $ LFPref 10)
  , (["if", "then"], LF $ LFPref 11)
  ]

test x = runState (parse $ makeTable ops) x
