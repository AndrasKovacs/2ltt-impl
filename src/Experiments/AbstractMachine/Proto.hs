
module Experiments.AbstractMachine.Proto where


{-
Abstract machine that supports unboxed returns and elided heap allocation
of intermediate closures.

We evaluate under a mutable array-based stack of values. The obvious benefit is O(1) indexing and
elision of heap allocations. We have to explicitly push and pop during execution.  In particular, we
need to correctly pop before tail calls to support tail recursion in constant space.

We have two evaluation modes/functions.

- Forced: the result is assumed to be required by an eliminator.
  This yields an unboxed sum as result.
- Unforced: the result will be stored in the environment. This yields a boxed
  value as result.

There is a design choice about function calls:
- Function calls are always evaluated in forced mode. This requires us to box returned values
  as an extra step whenever we make an unforced function call.
- Functions can be called both in forced and unforced mode. This is a bit more efficient, but
  - if functions are compiled to machine code or byte code, we have to compile function bodies
    twice and include two code pointers in closures
  - if functions are compiled to indirect threaded closures, we can share a lot of code between
    the two modes, but we still need two code pointers in closures

I use State and inefficient data representation for prototype purposes.
Bonus feature: do env stubbing after let-binding (called "stack stubbing" in GHC parlance)

NOTE:
 - if we use both forced and unforced function calls,
   then unboxed closures don't need to store the number of their args on stack,
   because we never convert from unboxed to boxed closures
-}

import Prelude hiding (lookup)
import Control.Monad.State.Strict
import Data.IORef

type Ix   = Int
data Trim = Id | Trim [Ix] deriving Show
type Pop  = Int
data Env  = Env {len :: Int, vals :: [Val]} deriving Show

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
pop n = modify' \(Env len vs) -> Env (len - n) (drop n vs)

lookup :: Ix -> State Env Val
lookup x = gets ((!!x) . vals)

push :: Env -> State Env ()
push (Env len vs) = modify' \(Env len' vs') -> Env (len + len') (vs ++ vs')

forced :: Tm -> State Env Val#
forced = \case
  Var p x -> do
    v <- lookup x
    pop p
    case v of
      Closure e t -> do push e; pure $! Closure# (len e) t
      VLit n      -> pure $! VLit# n
  App t u -> do
    v <- unforced u
    forced t >>= \case
      Closure# n t -> do push (Env 1 [v]); forced t
      _            -> typeError
  Lam p Id t ->
    pure $ Closure# p t
  Lam p (Trim is) t -> do
    capture <- mapM lookup is
    pop p
    let l = length capture
    push (Env l capture)
    pure $ Closure# l t
  Let t u -> do
    v <- unforced u
    push (Env 1 [v])
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

unforced :: Tm -> State Env Val
unforced = \case
  Var p x -> pop p >> lookup x
  App t u -> do
    v <- unforced u
    forced t >>= \case
      Closure# n t -> do push (Env 1 [v]); unforced t
      _            -> typeError
  Lam p Id t -> do
    Env l vs <- get
    put $! Env (l - p) (drop p vs)
    pure $! Closure (Env p (take p vs)) t
  Lam p (Trim is) t -> do
    capture <- mapM lookup is
    pop p
    pure $! Closure (Env (length capture) capture) t
  Let t u -> do
    v <- unforced u
    push (Env 1 [v])
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
