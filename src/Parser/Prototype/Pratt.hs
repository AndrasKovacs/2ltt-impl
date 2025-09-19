
{-# options_ghc -Wno-unused-imports -Wno-orphans #-}

module Parser.Prototype.Pratt where

import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Control.Applicative
import Control.Monad
import Debug.Trace
import Data.String

-- import Common
-- import Parser.Lexer
-- import qualified FlatParse.Stateful as FP

-- data Exp a
--   = Atom a
--   | Op String [Exp a]
--   deriving Show

-- type Prec = Int
-- type Op = String

-- data Table a
--   = Branch


--       (Map Op (Table a)) -- ^ closed operators, revert to max precedence

--   | Leaf [a]
--   deriving Show

-- type Parser b a = StateT [Either String b] (Except String) a

-- parse :: Table a -> Prec -> Parser a (Exp a)
-- parse tbl p = StateT \s -> case s of
--   []   -> throwError ""
--   x:xs -> case x of
--     Left op -> _
--     Right a -> _

-- parse :: Table -> Parser (Exp a)
-- parse = _



-- _+_ 2
-- _*_ 1
-- (_)

-- closed = parens add <|> lit
-- mul    = chainl1 (*) atom
-- add    = chainl1 (+) mul

-- op 0 = parens (op 2) <|> lit
-- op 1 = chainr1 (*) (op 0)
-- op 2 = chainr1 (+) (op 1)

{-

op p = case _ of
  (   -> op 2 <* )
  +   -> _
  *   -> _
  lit -> _


-}


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


-- Prattification
--------------------------------------------------------------------------------

type Op = String

data Exp = Lit Int | Add Exp Exp | Mul Exp Exp | Par Exp
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

-- closed, prefix
go :: Int -> Parser Exp
go p = peek >>= \case
  Just (Left i)    -> do pop; loop p (Lit i)
  Just (Right "(") -> do pop; t <- go 2; op ")"; loop p (Par t)
  _                -> empty

-- infix, postfix
loop :: Int -> Exp -> Parser Exp
loop p t = peek >>= \case
  Just (Right "+")
    | p < 2 -> pure t
    | True  -> do pop; u <- go 2; loop p (Add t u)
  Just (Right "*")
    | p < 1 -> pure t
    | True  -> do pop; u <- go 1; loop p (Mul t u)
  Just _  -> empty
  Nothing -> pure t

run :: Parser a -> [Either Int Op] -> Maybe (a, [Either Int Op])
run p s = runStateT p s

test s = run (go 2) s

--------------------------------------------------------------------------------
