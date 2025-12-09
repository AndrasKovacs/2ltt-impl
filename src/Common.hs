
module Common (
    module Common
  , module Control.Applicative
  , module Control.Exception
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
import Control.Exception
import Data.Bits
import Data.Foldable
import Data.IORef
import Data.List hiding (List)
import Data.Time.Clock
import Debug.Trace (trace, traceM, traceShow, traceShowM)
import GHC.Exts hiding (lazy, toList, List, BCO, mkApUpd0#, newBCO#)
import GHC.IO
import GHC.Word
import GHC.ForeignPtr
import IO (runIO)
import Lens.Micro
import Lens.Micro.TH
import Text.Show
import Data.Flat

import Data.ByteString.Char8 qualified as B
import Data.ByteString.Internal qualified as B
import FlatParse.Stateful qualified as FP

import Data.Hashable

import {-# source #-} Core.Syntax qualified as S


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

-- Overloaded application
--------------------------------------------------------------------------------

infixl 8 ∘
infixl 8 ∙
infixl 8 ∘~
infixl 8 ∙~
class Apply a b c | a -> b c where
  {-# inline (∙) #-}
  (∙)  :: a -> b -> c  -- ^ Explicit, strict
  (∙) a b = (∙∘) a (b, Expl)

  {-# inline (∘) #-}
  (∘)  :: a -> b -> c  -- ^ Implicit, strict
  (∘) a b = (∙∘) a (b, Impl)

  (∙~) :: a -> b -> c  -- ^ Explicit, lazy
  (∘~) :: a -> b -> c  -- ^ Implicit, lazy
  (∙~) = (∙); {-# inline (∙~) #-}
  (∘~) = (∘); {-# inline (∘~) #-}

  {-# inline (∙∘) #-}
  (∙∘) :: a -> (b, Icit) -> c
  (∙∘) a (!b, Expl) = a ∙ b
  (∙∘) a (!b, Impl) = a ∘ b

  {-# minimal (∙∘) | (∙), (∘) #-}

instance (Monad m, a ~ a', out ~ m b) => Apply (m (a -> b)) (m a') out where
  {-# inline (∙∘) #-}
  (∙∘) mf (ma, _) = do
    f <- mf
    a <- ma
    pure $! f a

-- Indexing
--------------------------------------------------------------------------------

class ElemAt a i b | a -> i b where
  elemAt   :: a -> i -> b

class UpdateAt a i b | a -> i b where
  updateAt :: a -> i -> (b -> b) -> a

instance ElemAt [a] Ix a where
  elemAt as i = as !! fromIntegral i

instance UpdateAt [a] Int a where
  {-# inline updateAt #-}
  updateAt as i f = go as i where
    go (a:as) 0 = f a : as
    go (a:as) i = (:) a $$! go as (i - 1)
    go _      _ = impossible

-- Strict list
--------------------------------------------------------------------------------

data List a = Nil | Cons a (List a)
  deriving (Eq, Ord)

type SnocList a = List a

instance Show a => Show (List a) where
  show = show . toList

instance Hashable a => Hashable (List a) where
  hashWithSalt h as = go h as `hashWithSalt` length as where
    go h Nil         = h
    go h (Cons a as) = go (hashWithSalt h a) as

pattern Single a = Cons a Nil
pattern Snoc as a = Cons a as
{-# complete Nil, Snoc #-}

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

  length = go 0 where
    go acc Nil = acc
    go acc (Cons _ as) = go (acc + 1) as

instance Traversable List where
  {-# inline traverse #-}
  traverse f = go where
    go Nil         = pure Nil
    go (Cons a as) = Cons <$> f a <*> go as

  {-# inline mapM #-}
  mapM f = go where
    go Nil         = pure Nil
    go (Cons a as) = Cons ! f a ∙ go as

instance ElemAt (List a) Ix a where
  elemAt as x = case (as, x) of
    (Cons a as, 0) -> a
    (Cons _ as, x) -> elemAt as (x - 1)
    _              -> impossible

instance UpdateAt (List a) Ix a where
  {-# inline updateAt #-}
  updateAt as i f = go as i where
    go (Cons a as) 0 = Cons (f a) as
    go (Cons a as) i = Cons a (go as (i - 1))
    go _           _ = impossible


-- reasonable monadic looping (forM_ and traverse are often compiled in shitty ways)
--------------------------------------------------------------------------------

class For t where
  for :: Monad m => t a -> (Lvl -> a -> m ()) -> m ()

instance For List where
  {-# inline for #-}
  for as f = go as 0 where
    go Nil         i = pure ()
    go (Cons a as) i = do f i a; go as (i + 1)

instance For [] where
  {-# inline for #-}
  for as f = go as 0 where
    go []       i = pure ()
    go (a : as) i = do f i a; go as (i + 1)


-- errors
--------------------------------------------------------------------------------

uf :: Dbg => a
uf = undefined
{-# noinline uf #-}

impossible :: Dbg => a
impossible = error "impossible"
{-# noinline impossible #-}

noStage0 :: Dbg => a
noStage0 = error "stage 0 not yet supported"
{-# noinline noStage0 #-}

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

infixl 9 $$!
($$!) :: (a -> b) -> a -> b
($$!) f a = f $! a
{-# inline ($$!) #-}

-- less annoying strict "idioms"
infixl 8 !
{-# inline (!) #-}
(!) :: Monad m => (a -> b) -> m a -> m b
(!) = (<$!>)

-- strict pair
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

type LvlArg = (?lvl :: Lvl)
{-# inline setLvl #-}
setLvl :: Lvl -> (LvlArg => a) -> a
setLvl l k = let ?lvl = l in k

lvlToIx :: Lvl -> Lvl -> Ix
lvlToIx (Lvl envl) (Lvl x) = Ix (envl - x - 1)
{-# inline lvlToIx #-}

ixToLvl :: Lvl -> Ix -> Lvl
ixToLvl (Lvl envl) (Ix x) = Lvl (envl - x - 1)
{-# inline ixToLvl #-}

--------------------------------------------------------------------------------

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

-- Source files
--------------------------------------------------------------------------------

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

-- Names and operators
--------------------------------------------------------------------------------

newtype RawName = RawName B.ByteString
  deriving (Eq, Ord, IsString) via B.ByteString

instance Hashable RawName where
  hashWithSalt h (RawName (B.PS (ForeignPtr p _) (I# start) (I# len))) = go h (plusAddr# p start) len where
    goBytes :: Int -> Addr# -> Int# -> Int
    goBytes h p len = case len of
      0# -> h
      _  -> goBytes (hashWithSalt h (W8# (indexWord8OffAddr# p 0#))) (plusAddr# p 1#) (len -# 1#)

    go :: Int -> Addr# -> Int# -> Int
    go h p len = case len <# 8# of
      1# -> goBytes h p len
      _  -> go (hashWithSalt h (W64# (indexWord64OffAddr# p 0#))) (plusAddr# p 8#) (len -# 8#)

instance Show RawName where
  show (RawName s) = FP.utf8ToStr s

data Name
  = NRawName RawName
  | NOp Operator
  | N_
  deriving (Eq, Ord)

instance Hashable Name where
  hashWithSalt h = \case
    NRawName x -> (h + 1) `hashWithSalt` x
    NOp op     -> (h + 2) `hashWithSalt` op
    N_         -> h + 3

instance Show Name where
  showsPrec p (NRawName x) acc = showsPrec p x acc
  showsPrec p N_           acc = '_':acc
  showsPrec p (NOp op)     acc = showsPrec p op acc

a_ = NRawName "a"
b_ = NRawName "b"
c_ = NRawName "c"
d_ = NRawName "d"
e_ = NRawName "e"
f_ = NRawName "f"
g_ = NRawName "g"
h_ = NRawName "h"
i_ = NRawName "i"
j_ = NRawName "j"
k_ = NRawName "k"
l_ = NRawName "l"
m_ = NRawName "m"
n_ = NRawName "n"
o_ = NRawName "o"
p_ = NRawName "p"
q_ = NRawName "q"
r_ = NRawName "r"
s_ = NRawName "s"
t_ = NRawName "t"
u_ = NRawName "u"
x_ = NRawName "x"
y_ = NRawName "y"
z_ = NRawName "z"

pattern A_ = NRawName "A"
pattern B_ = NRawName "B"
pattern C_ = NRawName "C"
pattern D_ = NRawName "D"
pattern P_ = NRawName "P"

newtype Precedence = Precedence Word
  deriving (Eq, Show, Num, Ord, Enum, Hashable) via Word

data Fixity
  = FInLeft Precedence   -- Infix left
  | FInRight Precedence  -- Infix right
  | FPre Precedence      -- Prefix
  | FPost Precedence     -- Postfix
  | FInNon Precedence    -- Infix non-associative
  | FClosed              -- Closed
  deriving (Eq, Ord, Show)

instance Hashable Fixity where
  hashWithSalt h = \case
    FInLeft x  -> h     `hashWithSalt` x
    FInRight x -> h + 1 `hashWithSalt` x
    FPre x     -> h + 2 `hashWithSalt` x
    FPost x    -> h + 3 `hashWithSalt` x
    FInNon x   -> h + 4 `hashWithSalt` x
    FClosed    -> h + 5

data Operator = Op Fixity (List RawName)
  deriving (Eq, Ord, Show)

instance Hashable Operator where
  hashWithSalt h (Op fix ops) = h `hashWithSalt` fix `hashWithSalt` ops

pick :: Name -> Name -> Name
pick N_ N_ = x_
pick x  N_ = x
pick _  y  = y

instance SpanOf RawName where
  leftPos  (RawName (B.PS _ start _))   = Pos $ FP.Pos start
  rightPos (RawName (B.PS _ start len)) = Pos $ FP.Pos (start + len)

instance SpanOf FP.Span where
  leftPos  (FP.Span x _) = Pos x
  rightPos (FP.Span _ x) = Pos x


-- Source positions & spans
--------------------------------------------------------------------------------

newtype Pos = Pos FP.Pos
  deriving Show via Int
  deriving (Eq,Ord) via FP.Pos

data Span = Span Pos Pos
  deriving Show via DontShow Span

{-# inline toSpan #-}
toSpan :: FP.Span -> Span
toSpan (FP.Span x y) = Span (coerce x) (coerce y)

type SpanArg = (?span :: Box Span)

spanToRawName :: SrcArg => Span -> RawName
spanToRawName (Span (Pos i) (Pos j)) =
  let bstr = srcToBs ?src
      i'   = B.length bstr - coerce i   -- Pos counts backwards from the end of the string
      j'   = B.length bstr - coerce j
  in RawName (B.take (j' - i') (B.drop i' bstr))

spanToString :: SrcArg => Span -> String
spanToString s = case spanToRawName s of RawName s -> FP.utf8ToStr s

class SpanOf a where
  spanOf  :: a -> Span
  spanOf a = Span (leftPos a) (rightPos a)

  leftPos :: a -> Pos
  leftPos a = case spanOf a of Span l _ -> l

  rightPos :: a -> Pos
  rightPos a = case spanOf a of Span _ r -> r

instance SpanOf Span where
  spanOf s = s

instance SpanOf Pos where
  leftPos  x = x
  rightPos x = x


-- Singletons
--------------------------------------------------------------------------------

data family Sing (x :: a)
data instance Sing (x :: Bool) where
  STrue  :: Sing 'True
  SFalse :: Sing 'False

class FromSing (x :: a) where sing :: Sing x
instance FromSing 'True  where sing = STrue
instance FromSing 'False where sing = SFalse


-- Primitives
--------------------------------------------------------------------------------

data Prim
  = Lift
  | Set
  | Ty
  | ValTy
  | CompTy
  | ElVal
  | ElComp
  | Eq
  | Refl
  | J
  | K
  | Fun0
  deriving (Eq, Show)

-- Overloaded accessors
--------------------------------------------------------------------------------

class Sized a where
  size :: a -> Lvl

instance Sized (List a) where
  size = go 0 where
    go acc Nil = acc
    go acc (Cons _ as) = go (acc + 1) as

class HasName s a | s -> a where
  name :: Lens' s a
  {-# minimal name #-}

class HasValue s a | s -> a where
  value :: Lens' s a
  {-# minimal value #-}

class HasIcit s a | s -> a where
  icit :: Lens' s a
  {-# minimal icit #-}

class HasClosure s a | s -> a where
  closure :: Lens' s a
  {-# minimal closure #-}

class HasLocals s a | s -> a where
  locals :: Lens' s a
  {-# minimal locals #-}

-- Projections
--------------------------------------------------------------------------------

data Proj = Proj {
    projIndex :: Ix
  , projName  :: Name
  } deriving Show

makeFields ''Proj


-- Unfolding options
--------------------------------------------------------------------------------

data Unfold = UnfoldNone | UnfoldAll | UnfoldMetas
  deriving (Eq, Show)

type UnfoldArg = (?unfold :: Unfold)

{-# inline setUnfold #-}
setUnfold :: Unfold -> (UnfoldArg => a) -> a
setUnfold uf k = let ?unfold = uf in k


-- Binders
--------------------------------------------------------------------------------

data Bind a = Bind {
    bindName :: Name
  , bindTy   :: S.Ty
  , bindBody :: a
  } deriving (Show, Functor, Foldable, Traversable)

data BindI a = BindI {
    bindIName :: Name
  , bindIIcit :: Icit
  , bindITy   :: S.Ty
  , bindIBody :: a
  } deriving (Show, Functor, Foldable, Traversable)

makeFields ''Bind
makeFields ''BindI
