
module Utils.Fusion where

-- import Common

-- newtype Push a = Push {unPush :: forall r. (a -> r -> r) -> r -> r}

-- class ToPush a b | a -> b where
--   push :: a -> Push b

-- class Collect a b | a -> b where
--   collect :: Push b -> a

-- instance a ~ b => ToPush (List a) b where
--   {-# inline push #-}
--   push as = Push \c ~n ->
--     let go Nil         = n
--         go (Cons a as) = c a (go as)
--         {-# inline go #-}
--     in go as

-- instance a ~ b => Collect (List a) b where
--   {-# inline collect #-}
--   collect (Push f) = f Cons Nil

-- --------------------------------------------------------------------------------

-- instance Functor Push where
--   {-# inline fmap #-}
--   fmap f (Push as) = Push (lam1 \c -> lam1 \ ~n -> as (lam1 \a -> lam1 \ ~bs -> c (f a) bs) n)
--   {-# inline (<$) #-}
--   (<$) = fmap . const

-- instance Applicative Push where
--   {-# inline pure #-}
--   pure a = Push (lam1 \c -> lam1 \ ~n -> c a n)
--   {-# inline (<*>) #-}
--   Push fs <*> Push as = Push (lam1 \c -> lam1 \ ~n ->
--     fs (lam1 \f -> lam1 \ ~r -> as (lam1 \a -> lam1 \ ~r -> c (f a) r) r) n)

-- instance Monad Push where
--   {-# inline return #-}
--   return = pure
--   {-# inline (>>=) #-}
--   Push as >>= f = Push (lam1 \c -> lam1 \ ~n -> as (lam1 \a -> lam1 \ ~r -> unPush (f a) c r) n)

-- instance Semigroup (Push a) where
--   {-# inline (<>) #-}
--   Push as <> Push bs = Push (lam1 \c -> lam1 \ ~n -> as c (bs c n))

-- instance Monoid (Push a) where
--   {-# inline mempty #-}
--   mempty = Push (lam1 \c -> lam1 \ ~n -> n)

-- {-# inline filter #-}
-- filter :: (a -> Bool) -> Push a -> Push a
-- filter f (Push as) = Push (lam1 \c -> lam1 \ ~n ->
--   as (lam1 \a -> lam1 \ ~r -> if f a then c a r else r) n)

-- instance Alternative Push where
--   {-# inline empty #-}
--   empty = mempty
--   {-# inline (<|>) #-}
--   (<|>) = (<>)

-- instance Foldable Push where
--   {-# inline foldr #-}
--   foldr f b (Push as) = as f b

--   {-# inline foldl' #-}
--   foldl' f b (Push as) =
--     as (lam1 \a -> lam1 \hyp -> lam1 \b -> f $$! hyp b $$! a) (lam1 \b -> b) b

--   {-# inline length #-}
--   length = foldl' (lam1 \acc -> lam1 \ ~_ -> acc + 1) 0

--   {-# inline null #-}
--   null (Push as) = as (\_ _ -> False) True

--   {-# inline sum #-}
--   sum = foldl' (+) 0

--   {-# inline product #-}
--   product = foldl' (*) 1

-- {-# inline range #-}
-- range :: (Enum a, Ord a) => a -> a -> Push a
-- range lo hi = Push (lam1 \c -> lam1 \ ~n ->
--   let go lo hi | lo >= hi = n
--       go lo hi = c lo (go (succ lo) hi)
--   in go lo hi)

-- --------------------------------------------------------------------------------

-- instance a ~ b => Collect [a] b where
--   {-# inline collect #-}
--   collect (Push as) = as (:) []

-- instance a ~ b => ToPush [a] b where
--   {-# inline push #-}
--   push as = Push \c ~n ->
--     let go []       = n
--         go (a : as) = c a (go as)
--         {-# inline go #-}
--     in go as

-- -- testing
-- --------------------------------------------------------------------------------

-- test1 :: Int -> Int
-- test1 i = foldl' (+) 0 (range 0 i)

-- test2 :: List Int -> Int
-- test2 ~xs = length do
--   x <- push xs
--   if x < 30 then do
--     foo <- push xs
--     pure (foo * x)
--   else
--     mempty

-- test3 :: [Int] -> Int
-- test3 xs = length do
--   x <- xs
--   guard (x < 30)
--   let y = x * 30
--   foo <- xs
--   pure (foo * y)
