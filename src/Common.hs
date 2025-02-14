
module Common (
    module Common
  , module Control.Monad
  , module Data.Bits
  , module Lens.Micro
  , module Lens.Micro.TH
  , module Data.IORef
  , module GHC.Exts
  , module GHC.Word
  , module Text.Show
  , module Data.Foldable
  , FP.utf8ToStr
  , FP.strToUtf8
  , runIO
  , trace
  , traceM
  , traceShow
  , traceShowM) where

import Control.Monad
import Data.Bits
import Data.Foldable
import Data.IORef
import Data.List
import Data.Time.Clock
import Debug.Trace (trace, traceM, traceShow, traceShowM)
import GHC.Exts hiding (lazy, toList)
import GHC.IO
import GHC.Word
import IO (runIO)
import Lens.Micro
import Lens.Micro.TH
import Text.Show

import qualified Data.ByteString.Char8 as B
import qualified FlatParse.Stateful as FP

-- Debug printing, toggled by "debug" cabal flag
--------------------------------------------------------------------------------

#define DEBUG

#ifdef DEBUG
import GHC.Stack
#endif

#ifdef DEBUG
type Dbg = HasCallStack

debug :: [String] -> IO ()
debug strs = putStrLn (intercalate " | " strs ++ " END")

debugging :: IO () -> IO ()
debugging act = act
{-# inline debugging #-}
#else
type Dbg = () :: Constraint

debug :: [String] -> IO ()
debug strs = pure ()
{-# inline debug #-}

debugging :: IO () -> IO ()
debugging _ = pure ()
{-# inline debugging #-}
#endif

debug' :: [String] -> IO ()
debug' strs = putStrLn (intercalate " | " strs ++ " END")

debugging' :: IO () -> IO ()
debugging' act = act
{-# inline debugging' #-}

noinlineRunIO :: IO a -> a
noinlineRunIO (IO f) = runRW# (\s -> case f s of (# _, a #) -> a)
{-# noinline noinlineRunIO #-}

-- errors
----------------------------------------------------------------------------------------------------

uf :: Dbg => a
uf = undefined
{-# noinline uf #-}

impossible :: Dbg => a
impossible = error "impossible"
{-# noinline impossible #-}

-- strictness & primops
-------------------------------------------------------------------------------------------

ctz :: Word -> Word
ctz (W# n) = W# (ctz# n)
{-# inline ctz #-}

clz :: Word -> Word
clz (W# n) = W# (clz# n)
{-# inline clz #-}

i2w :: Int -> Word
i2w (I# n) = W# (int2Word# n)
{-# inline i2w #-}

w2i :: Word -> Int
w2i (W# n) = I# (word2Int# n)
{-# inline w2i #-}

($$!) :: (a -> b) -> a -> b
($$!) f a = f $! a
{-# inline ($$!) #-}
infixl 9 $$!

infixl 4 <*!>
(<*!>) :: Monad m => m (a -> b) -> m a -> m b
(<*!>) mf ma = do
  f <- mf
  a <- ma
  pure $! f a
{-# inline (<*!>) #-}

infixr 4 //
(//) :: a -> b -> (a, b)
a // b = (a, b)
{-# inline (//) #-}

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

data Box a = Box ~a deriving Show

-- Not printing stuff
--------------------------------------------------------------------------------

newtype DontShow a = DontShow {unDontShow :: a} deriving Eq

instance Show (DontShow a) where
  showsPrec _ _ x = x

-- De Bruijn
--------------------------------------------------------------------------------

newtype Ix = Ix {unIx :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real) via Word

newtype Lvl = Lvl {unLvl :: Word}
  deriving (Eq, Ord, Show, Num, Enum, Bits, Integral, Real) via Word

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl x) = Ix (envl - x - 1)
{-# inline lvlToIx #-}

ixToLvl :: Lvl -> Ix -> Lvl
ixToLvl (Lvl envl) (Ix x) = Lvl (envl - x - 1)
{-# inline ixToLvl #-}

-- Time measurement
--------------------------------------------------------------------------------

-- | Time an IO computation. Result is forced to whnf.
timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1  <- getCurrentTime
  res <- a
  t2  <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)
{-# inline timed #-}

-- | Time a lazy pure value. Result is forced to whnf.
timedPure :: a -> IO (a, NominalDiffTime)
timedPure ~a = do
  t1  <- getCurrentTime
  let res = a
  t2  <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)
{-# noinline timedPure #-}

-- | Time a lazy pure value. Result is forced to whnf.
timedPure_ :: a -> IO NominalDiffTime
timedPure_ ~a = do
  t1  <- getCurrentTime
  seq a $ do
    t2  <- getCurrentTime
    let diff = diffUTCTime t2 t1
    pure diff
{-# noinline timedPure_ #-}

-- names
--------------------------------------------------------------------------------

data Name
  = NSpan {-# unpack #-} Span
  | NGeneric B.ByteString
  | N_
  deriving (Eq)

instance Show Name where
  show (NSpan x)    = show x
  show (NGeneric x) = B.unpack x
  show N_           = "_"

nameToBs :: SrcArg => Name -> B.ByteString
nameToBs = \case
  NSpan x    -> spanToBs x
  NGeneric x -> x
  N_         -> "_"

data Src
  = SrcFile FilePath B.ByteString
  | SrcImpossible                   -- ^ Impossible case just for killing unboxing.

instance Show Src where
  show (SrcFile fp _) = "File " ++ fp
  show  SrcImpossible = impossible

srcToBs :: Src -> B.ByteString
srcToBs (SrcFile _ bs)   = bs
srcToBs SrcImpossible    = impossible

type SrcArg = (?src :: Src)

a_ = NGeneric "a"
b_ = NGeneric "b"
c_ = NGeneric "c"
d_ = NGeneric "d"
e_ = NGeneric "e"
f_ = NGeneric "f"
g_ = NGeneric "g"
h_ = NGeneric "h"
i_ = NGeneric "i"
j_ = NGeneric "j"
k_ = NGeneric "k"
l_ = NGeneric "l"
m_ = NGeneric "m"
n_ = NGeneric "n"
o_ = NGeneric "o"
p_ = NGeneric "p"
q_ = NGeneric "q"
r_ = NGeneric "r"
s_ = NGeneric "s"
t_ = NGeneric "t"
u_ = NGeneric "u"
x_ = NGeneric "x"
y_ = NGeneric "y"
z_ = NGeneric "z"

-- source positions & spans
--------------------------------------------------------------------------------

type Pos = FP.Pos
type Span = FP.Span

spanToBs :: SrcArg => Span -> B.ByteString
spanToBs (FP.Span i j) =
  let bstr = srcToBs ?src
      i'   = B.length bstr - coerce i   -- Pos counts backwards from the end of the string
      j'   = B.length bstr - coerce j
  in B.take (j' - i') (B.drop i' bstr)

spanToString :: SrcArg => Span -> String
spanToString s = FP.utf8ToStr (spanToBs s)
