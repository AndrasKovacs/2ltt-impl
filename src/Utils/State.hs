
module Utils.State where

import GHC.Exts (oneShot)

newtype State s a = State {runState# :: s -> (# a, s #)}

instance Functor (State s) where
  {-# inline fmap #-}
  fmap f (State g) = State (oneShot \s -> case g s of
    (# a, !s #) -> let b = f a in (# b, s #))
  {-# inline (<$) #-}
  (<$) a m = (\_ -> a) <$> m

instance Applicative (State s) where
  {-# inline pure #-}
  pure a = State (oneShot \s -> (# a, s #))
  {-# inline (<*>) #-}
  State mf <*> State ma = State (oneShot \s -> case mf s of
    (# f, s #) -> case ma s of
      (# a, !s #) -> let b = f a in (# b, s #))
  {-# inline (*>) #-}
  State ma *> State mb = State (oneShot \s -> case ma s of
    (# _, s #) -> mb s)
  {-# inline (<*) #-}
  State ma <* State mb = State (oneShot \s -> case ma s of
    (# a, s #) -> case mb s of
      (# _, s #) -> (# a, s #))

instance Monad (State s) where
  {-# inline return #-}
  return = pure
  {-# inline (>>=) #-}
  State ma >>= f = State (oneShot \s -> case ma s of
    (# a, s #) -> runState# (f a) s)
  {-# inline (>>) #-}
  (>>) = (*>)

{-# inline put #-}
put :: s -> State s ()
put s = State (oneShot \_ -> (# (), s #))

{-# inline get #-}
get :: State s s
get = State (oneShot \s -> (# s, s #))

{-# inline gets #-}
gets :: (s -> a) -> State s a
gets f = f <$> get

{-# inline modify #-}
modify :: (s -> s) -> State s ()
modify f = State (oneShot \s -> let s' = f s in (# (), s' #))

{-# inline execState #-}
execState :: State s a -> s -> s
execState (State f) s = case f s of
  (# _, s #) -> s

{-# inline runState #-}
runState :: State s a -> s -> (a, s)
runState (State f) s = case f s of
  (# !a, !s #) -> (a, s)

{-# inline evalState #-}
evalState :: State s a -> s -> a
evalState (State f) s = case f s of
  (# a, _ #) -> a
