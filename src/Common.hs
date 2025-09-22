
module Common (
    module Common
  , module Control.Applicative
  , module Control.Monad
  , module Data.Bits
  , module Data.Foldable
  , module Data.IORef
  , module GHC.Exts
  , module GHC.Word
  , module Lens.Micro
  , module Lens.Micro.TH
  , module Text.Show
  , FP.utf8ToStr
  , FP.strToUtf8
  , runIO
  , trace
  , traceM
  , traceShow
  , traceShowM) where

import Control.Applicative
import Control.Monad
import Data.Bits
import Data.Foldable
import Data.IORef
import Data.List hiding (List)
import Data.Time.Clock
import Debug.Trace (trace, traceM, traceShow, traceShowM)
import GHC.Exts hiding (lazy, toList, List, BCO, mkApUpd0#, newBCO#)
import GHC.IO
import GHC.Word
import IO (runIO)
import Lens.Micro
import Lens.Micro.TH
import Text.Show
import Data.Flat

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

debugM :: Monad m => [String] -> m ()
debugM strs = traceM (intercalate " | " strs ++ " END")

debug :: [String] -> IO ()
debug strs = putStrLn (intercalate " | " strs ++ " END")

debugging :: IO () -> IO ()
debugging act = act
{-# inline debugging #-}
#else
type Dbg = () :: Constraint

debugM :: Monad m => [String] -> m ()
debugM _ = pure ()
{-# inline debugM #-}

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


-- Strict list
--------------------------------------------------------------------------------

data List a = Nil | Cons a (List a)
  deriving (Eq, Ord, Show)

pattern Single a = Cons a Nil

instance Functor List where
  fmap f = go where
    go Nil = Nil
    go (Cons a as) = Cons (f a) (go as)
  {-# inline fmap #-}
  (<$) a as = fmap (\_ -> a) as
  {-# inline (<$) #-}

instance Semigroup (List a) where
  Nil <> as = as
  Cons a as <> as' = Cons a (as <> as')

instance Monoid (List a) where
  mempty = Nil
  {-# inline mempty #-}

instance Foldable List where
  {-# inline foldr #-}
  foldr f ~b as = go as where
    go Nil = b
    go (Cons a as) = f a (go as)

  {-# inline foldl' #-}
  foldl' f b as = go as b where
    go Nil         b = b
    go (Cons a as) b = go as (f b a)

instance Traversable List where
  {-# inline traverse #-}
  traverse f = go where
    go Nil         = pure Nil
    go (Cons a as) = Cons <$> f a <*> go as

  {-# inline mapM #-}
  mapM f = go where
    go Nil         = pure Nil
    go (Cons a as) = Cons <$!> f a ∙ go as

-- errors
--------------------------------------------------------------------------------

uf :: Dbg => a
uf = undefined
{-# noinline uf #-}

impossible :: Dbg => a
impossible = error "impossible"
{-# noinline impossible #-}

-- strictness & primops
--------------------------------------------------------------------------------

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

-- less annoying strict "idioms"
infixl 4 !
{-# inline (!) #-}
(!) :: Monad m => (a -> b) -> m a -> m b
(!) = (<$!>)

infixl 4 ∙
(∙) :: Monad m => m (a -> b) -> m a -> m b
(∙) mf ma = do
  f <- mf
  a <- ma
  pure $! f a
{-# inline (∙) #-}

-- strict pair
infixr 4 //
(//) :: a -> b -> (a, b)
a // b = (a, b)
{-# inline (//) #-}

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

data Box a = Box ~a deriving Show

lam1 :: (a -> b) -> a -> b
lam1 = oneShot
{-# inline lam1 #-}

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

type LvlArg = (?lvl :: Lvl)

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl x) = Ix (envl - x - 1)
{-# inline lvlToIx #-}

ixToLvl :: Lvl -> Ix -> Lvl
ixToLvl (Lvl envl) (Ix x) = Lvl (envl - x - 1)
{-# inline ixToLvl #-}

--------------------------------------------------------------------------------

-- | Ordinary metavariable.
newtype MetaVar = MkMetaVar Int
  deriving (Eq, Ord, Num, Flat) via Int

instance Show MetaVar where
  showsPrec _ (MkMetaVar x) acc = '?': showsPrec 0 x acc

--------------------------------------------------------------------------------

data Stage = S0 | S1
  deriving (Eq, Show, Ord, Enum)

data Icit = Impl | Expl
  deriving (Eq, Show, Ord, Enum)

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
  | NOp {-# unpack #-} Operator
  | NGeneric B.ByteString
  | N_
  deriving (Eq)

instance Show Name where
  showsPrec p (NSpan x)    acc = showsPrec p x acc
  showsPrec p (NGeneric x) acc = B.unpack x ++ acc
  showsPrec p N_           acc = '_':acc
  showsPrec p (NOp op)     acc = showsPrec p op acc

opToBs :: SrcArg => Operator -> B.ByteString
opToBs (Op f xs) = uf

nameToBs :: SrcArg => Name -> B.ByteString
nameToBs = \case
  NSpan x    -> spanToBs x
  NGeneric x -> x
  N_         -> "_"
  NOp op     -> opToBs op

data Src
  = SrcFile FilePath B.ByteString
  | SrcDontUnbox

instance Show Src where
  show (SrcFile fp _) = "File " ++ fp
  show SrcDontUnbox   = impossible

srcToBs :: Src -> B.ByteString
srcToBs (SrcFile _ bs) = bs
srcToBs SrcDontUnbox   = impossible

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

newtype Precedence = Precedence Word
  deriving (Eq, Show, Num, Ord, Enum) via Word

data Fixity
  = FInLeft Precedence   -- Infix left
  | FInRight Precedence  -- Infix right
  | FPre Precedence      -- Prefix
  | FPost Precedence     -- Postfix
  | FInNon Precedence    -- Infix non-associative
  | FClosed              -- Closed
  deriving (Eq, Show)

data Operator = Op Fixity (List Span)
  deriving (Eq, Show)

-- projection
data Proj
  = PNoName Int
  | PName Int Name
  deriving Show

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

class SpanOf a where
  spanOf  :: a -> Span
  spanOf a = FP.Span (leftPos a) (rightPos a)

  leftPos :: a -> Pos
  leftPos a = case spanOf a of FP.Span l _ -> l

  rightPos :: a -> Pos
  rightPos a = case spanOf a of FP.Span _ r -> r

instance SpanOf Span where
  spanOf s = s

instance SpanOf Pos where
  leftPos  x = x
  rightPos x = x

--------------------------------------------------------------------------------

data family Sing (x :: a)
data instance Sing (x :: Bool) where
  STrue  :: Sing 'True
  SFalse :: Sing 'False

class FromSing (x :: a) where sing :: Sing x
instance FromSing 'True  where sing = STrue
instance FromSing 'False where sing = SFalse
