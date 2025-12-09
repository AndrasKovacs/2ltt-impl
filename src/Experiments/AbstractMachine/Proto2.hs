

module Experiments.AbstractMachine.Proto2 where

import Prelude hiding (lookup)
import Control.Monad.State.Strict
import Data.IORef

type Ix   = Int
data Trim = Id | Trim [Ix] deriving Show
type Pop  = Int
type Env = [Val]

data Tm
  = Var Pop Ix
  | App Tm Tm
  | Lam Pop Trim Tm
  | Let Tm Tm
  | Lit Pop Int
  | Add Pop Tm Tm
  deriving Show

data Val = Closure Env Tm | VLit Int  deriving Show

-- This is supposed to be an unboxed sum.
data Val#
  = Closure# Int Tm  -- number of function arguments on the top of the env, body
  | VLit# Int
  deriving Show

typeError :: a
typeError = error "type error"

pop :: Int -> State Env ()
pop n = modify' (drop n)

lookup :: Ix -> State Env Val
lookup x = gets (!!x)

push :: Env -> State Env ()
push vs = modify' (vs++)

forced :: Tm -> State Env Val#
forced = \case
  Var p x -> do
    v <- lookup x
    pop p
    case v of
      Closure e t -> do push e; pure $! Closure# (length e) t
      VLit n      -> pure $! VLit# n
  App t u -> do
    v <- unforced u
    forced t >>= \case
      Closure# n t -> do push [v]; forced t
      _            -> typeError
  Lam p Id t ->
    pure $ Closure# p t
  Lam p (Trim is) t -> do
    capture <- mapM lookup is
    pop p
    push capture
    pure $! Closure# (length capture) t
  Let t u -> do
    v <- unforced u
    push [v]
    forced t
  Lit p n -> do
    pop p
    pure $ VLit# n
  Add p t u -> do
    v  <- forced t
    v' <- forced u
    pop p
    case (v, v') of
      (VLit# n, VLit# n') -> pure $! VLit# (n + n')
      _                   -> typeError

box :: Val# -> State Env Val
box = \case
  Closure# l t -> do vs <- get; pure $! Closure (take l vs) t
  VLit# n      -> pure $ VLit n

unforced :: Tm -> State Env Val
unforced = \case
  Var p x -> pop p >> lookup x
  App t u -> do
    v <- unforced u
    forced t >>= \case
      Closure# n t -> do push [v]; forced t >>= box
      _            -> typeError
  Lam p Id t -> do
    vs <- get
    put $! drop p vs
    pure $! Closure (take p vs) t
  Lam p (Trim is) t -> do
    capture <- mapM lookup is
    pop p
    pure $! Closure capture t
  Let t u -> do
    v <- unforced u
    push [v]
    unforced u
  Lit p n -> do
    pop p
    pure $ VLit n
  Add p t u -> do
    x <- forced t
    y <- forced u
    pop p
    case (x, y) of
      (VLit# n, VLit# n') -> pure $! VLit (n + n')
      _                   -> typeError











--------------------------------------------------------------------------------
