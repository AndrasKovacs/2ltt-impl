
{-# options_ghc -Wno-unused-imports -Wno-orphans #-}

module Parser.Prototype.Pratt where

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

-- type Parser a = StateT [Either Int Op] Maybe a

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
--   _ -> empty

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
--       _                 -> empty}
--     _ -> empty

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
--       | nonfix == Just 15 -> empty
--       | True              -> do pop; u <- go 10; loop p (Just 15) (Op "_==_" [t, u])
--     Just _  -> empty
--     Nothing -> pure t

-- run :: Parser a -> [Either Int Op] -> Maybe (a, [Either Int Op])
-- run p s = runStateT p s
-- test s = run (go 20) s

--------------------------------------------------------------------------------

type Op = String

data Exp = Lit Int | Op Op [Exp]
  deriving Show

type Parser a = StateT [Either Int Op] Maybe a

instance IsString (Either a String) where
  fromString = Right

instance Num (Either Int a) where
  fromInteger = Left . fromIntegral
  (+) = undefined; (*) = undefined; abs = undefined
  signum = undefined; negate = undefined

peek :: Parser (Maybe (Either Int Op))
peek = get >>= \case
  []   -> pure Nothing
  x:xs -> pure (Just x)

pop :: Parser ()
pop = modify (drop 1)

op :: Op -> Parser ()
op str = peek >>= \case
  Just (Right str') | str == str' -> pop
  _ -> empty

-- Prefix and closed operators
type LeftTable = Map Op LeftNode
data LeftNode  = LNode (Set LFixity) LeftTable deriving Show

-- Infix and postfix operators
type InTable = Map Op InNode
data InNode  = INode Int (Set IFixity) InTable deriving Show

data LFixity = LFClosed | LFPref Int deriving (Show, Eq, Ord)
data IFixity = IFLeft Int | IFRight Int | IFNon Int | IFPost Int deriving (Eq, Ord, Show)
data Fixity  = LF LFixity | IF IFixity deriving Show

prec :: IFixity -> Int
prec = \case
  IFLeft p -> p
  IFRight p -> p
  IFNon p -> p
  IFPost p -> p

type Operator = ([Op], Fixity) -- nonempty list
type Table = (LeftNode, InNode)

insert :: Operator -> Table -> Table
insert (ops, f) (lt, it) = case f of
  LF f -> (insertL ops f lt, it)
  IF f -> (lt, insertI ops f it)

insertL :: [Op] -> LFixity -> LeftNode -> LeftNode
insertL []       f (LNode fs t) = LNode (Set.insert f fs) t
insertL (op:ops) f (LNode fs t) =
  LNode fs $ Map.insertWith
    (\_ -> insertL ops f)
    op
    (insertL ops f (LNode mempty mempty))
    t

insertI :: [Op] -> IFixity -> InNode -> InNode
insertI []       f (INode p fs t) = INode (max p (prec f)) (Set.insert f fs) t
insertI (op:ops) f (INode p fs t) =
  INode (max p (prec f)) fs $ Map.insertWith
    (\_ -> insertI ops f)
    op
    (insertI ops f (INode 0 mempty mempty))
    t

ops :: [Operator]
ops = [
    (["+"], IF $ IFLeft 5)
  , (["*"], IF $ IFLeft 6)
  , (["(",")"], LF $ LFClosed)
  ]

makeTable :: [Operator] -> Table
makeTable = foldl' (flip insert) (LNode mempty mempty, INode 0 mempty mempty)

parse :: Table -> Parser Exp
parse (lt, it) = left 0 where

  -- we need to accummulate args during trie-walking, because we
  -- can't patch the result up on the way back

  walkLeft :: Int -> Op -> LeftNode -> Parser (Op, [Exp])
  walkLeft p op (LNode _ t) = case Map.lookup op t of
    Just (LNode fs t)
      -- unambiguous end
      | [f] <- Set.toList fs, Map.null t ->
          case f of
            LFClosed  -> pure _
            LFPref p' -> _

      -- continue
      | Set.null fs -> do
          t <- left 0
          peek >>= \case
            Just (Left i)    -> _
            Just (Right op') -> _
            Nothing          -> _
      | True ->
          error "ambigous grammar"
    Nothing ->
      empty

  left :: Int -> Parser Exp
  left p = peek >>= \case
    Just (Left i)   -> do pop; inside p (Lit i)
    Just (Right op) -> do pop; (f, xs) <- walkLeft p op lt; pure (Op f xs)
    Nothing         -> empty

  inside :: Int -> Exp -> Parser Exp
  inside p t = _

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
--       _                 -> empty}
--     _ -> empty

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
--       | nonfix == Just 15 -> empty
--       | True              -> do pop; u <- go 10; loop p (Just 15) (Op "_==_" [t, u])
--     Just _  -> empty
--     Nothing -> pure t

-- run :: Parser a -> [Either Int Op] -> Maybe (a, [Either Int Op])
-- run p s = runStateT p s
-- test s = run (go 20) s

--------------------------------------------------------------------------------
