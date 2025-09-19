
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

-- data Table
