{-# options_ghc -Wno-unused-imports -Wno-type-defaults #-}

{-

TODO optimization: pop the stack exactly when a suffix of it goes unused
-}

module Experiments.AbstractMachine.Proto3 where

import Control.Monad
import Control.Monad.State.Strict hiding (lift)
import Data.IORef
import Data.IntSet (IntSet)
import Data.IntSet qualified as IS
import Data.Maybe
import Data.String
import Debug.Trace
import System.IO.Unsafe

type Ix   = Int
type Lvl  = Int
data Trim = Id | Trim [Ix] deriving Show
type Pop  = Int
type Env  = [Val]

data Tm
  = Var Pop Ix
  | App Tm Tm
  | Lam Pop Trim Tm
  | Let Tm Tm
  | Lit Pop Int
  | Add Pop Tm Tm
  deriving Show

data Val = Closure Env Tm | VLit Int deriving Show

-- This is supposed to be an unboxed sum.
data Val#
  = Closure# Int Tm  -- number of function arguments on the top of the env, body
  | VLit# Int
  deriving Show

-- Compiling raw terms
--------------------------------------------------------------------------------

type Name = String

data RTm
  = RVar Name
  | RApp RTm RTm
  | RLam Name RTm
  | RLet Name RTm RTm
  | RLit Int
  | RAdd RTm RTm
  deriving Show

instance Num RTm where
  fromInteger = RLit . fromIntegral
  (+) = RAdd
  (*) = undefined; abs = undefined; signum = undefined; negate = undefined

instance IsString RTm where
  fromString = RVar

infixl 8 ∙
(∙) = RApp

data LTm
  = LVar Lvl
  | LApp LTm LTm
  | LLam [Lvl] Tm
  | LLet LTm LTm
  | LLit Int
  | LAdd LTm LTm
  deriving Show

data Ren = Ren {dom :: Lvl, cod :: Lvl, ren :: [(Lvl, Lvl)]}
  deriving Show

lift :: Ren -> Ren
lift (Ren d c r) = Ren (d + 1) (c + 1) ((c, d):r)

comp :: RTm -> [(Name, Lvl)] -> Lvl -> State IntSet LTm
comp t env l = case t of
  RVar x -> case lookup x env of
    Nothing -> error $ "name not in scope: " ++ x
    Just x  -> do modify' (IS.insert x); pure $ LVar x
  RApp t u -> do
    t <- comp t env l
    u <- comp u env l
    pure $ LApp t u
  RLam x t -> do
    oldfvs <- get
    put mempty
    t <- comp t ((x, l) : env) (l + 1)
    fvs <- IS.delete l <$> get
    let fvlist = IS.toList fvs
    let r  = Ren (length fvlist) l (zip fvlist [0..])
    let t' = comp' t (lift r) 0
    put $! oldfvs <> fvs
    pure $! LLam fvlist t'
  RLet x t u -> do
    t <- comp t env l
    u <- comp u ((x, l):env) (l + 1)
    modify' $ IS.delete l
    pure $ LLet t u
  RLit n -> pure $ LLit n
  RAdd t u -> do
    t <- comp t env l
    u <- comp u env l
    pure $ LAdd t u

comp' :: LTm -> Ren -> Lvl -> Tm
comp' t r base = case t of
  LVar x ->
    let x' = fromJust (lookup x (ren r))
    in Var (dom r - base) (dom r - x' - 1)
  LApp t u -> App (comp' t r base) (comp' u r 0)
  LLam xs t ->
    let xs' = map (\x -> fromJust $ lookup x (ren r)) xs
        trim | xs' == [0..dom r - 1] = Id
             | otherwise             = Trim xs'
    in Lam (dom r - base) trim t
  LLet t u ->
    let t' = comp' t r (dom r)
        u' = comp' u (lift r) base
    in Let t' u'
  LLit n -> Lit (dom r - base) n
  LAdd t u -> Add (dom r - base) (comp' t r (dom r)) (comp' u r (dom r))

compile :: RTm -> Tm
compile t = comp' (evalState (comp t [] 0) mempty) (Ren 0 0 []) 0

--------------------------------------------------------------------------------

stack :: IORef [Val]
stack = unsafePerformIO $ newIORef []

typeError :: a
typeError = error "type error"

pop :: Int -> IO ()
pop 0 = pure ()
pop n = modifyIORef' stack (drop n)

readStack :: IO [Val]
readStack = readIORef stack

writeStack :: [Val] -> IO ()
writeStack = writeIORef stack

index :: Ix -> IO Val
index x = (!!x) <$!> readStack

push :: Env -> IO ()
push vs = modifyIORef' stack (vs++)

--------------------------------------------------------------------------------

forced :: Tm -> IO Val#
forced = \case
  Var p x -> do
    v <- index x
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
    capture <- mapM index is
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

box :: Val# -> IO Val
box = \case
  Closure# l t -> do vs <- readStack; pure $! Closure (take l vs) t
  VLit# n      -> pure $ VLit n

unforced :: Tm -> IO Val
unforced = \case
  Var p x -> do
    v <- index x
    pop p
    pure v
  App t u -> do
    v <- unforced u
    forced t >>= \case
      Closure# n t -> do push [v]; unforced t
      _            -> typeError
  Lam p Id t -> do
    vs <- readStack
    writeStack $! drop p vs
    pure $! Closure (take p vs) t
  Lam p (Trim is) t -> do
    capture <- mapM index is
    pop p
    pure $! Closure capture t
  Let t u -> do
    v <- unforced t
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


run :: RTm -> IO Val
run t = do
  writeStack []
  unforced $ compile t


--------------------------------------------------------------------------------

x_ = "x" :: RTm
y_ = "y" :: RTm
z_ = "z" :: RTm
a_ = "a" :: RTm
b_ = "b" :: RTm
c_ = "c" :: RTm
d_ = "d" :: RTm
e_ = "e" :: RTm
f_ = "f" :: RTm
g_ = "g" :: RTm
h_ = "h" :: RTm

lx = RLam "x"
ly = RLam "y"
lz = RLam "z"
la = RLam "a"
lb = RLam "b"
lc = RLam "c"
ld = RLam "d"
le = RLam "e"
lf = RLam "f"
lg = RLam "g"
lh = RLam "h"
let_ = RLet

t =
  let_ "f" (lx $ x_ + 1000) $
  let_ "g" (lx $ x_ + 2000) $














  1000














--------------------------------------------------------------------------------
