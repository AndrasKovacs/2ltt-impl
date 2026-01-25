
module Fusion where

import Control.Monad.Reader

-- Sum
--------------------------------------------------------------------------------

f :: Int -> Reader Bool Int
f x = do
  b <- ask
  if b then return (x + 10)
       else return (x + 20)

-- f1 :: [Int] -> [Int]
-- f1 = map (*2) . map (*10)

-- go = \x -> x * 20
-- f1 = \xs -> map go xs

-- f1 = \xs -> case xs of
--   []   -> []
--   x:xs -> (x * 20) : f1 xs

-- f2 :: [Int] -> Int
-- f2 = sum . f1

-- go xs acc = case xs of
--   []   -> acc
--   x:xs -> go xs (acc + x)
-- f2 = \xs -> go xs 0



-- -- FAILS
-- f2 :: Int -> Int -> Int
-- f2 x y = sum $ map (*4) $ map (*2) $ map (*3) [x..y]

-- f = \x -> x * 20
-- f2 = \xs -> map f xs

-- f = \case
--   []   -> []
--   x:xs -> (x * 20) : f xs



-- f3 :: Int -> Int -> Int
-- f3 x y = sum $ take 100 $ map (+10) [x..y]




-- -- FAIL: compiles to foldl' (+) 0 without inlining.
-- sumList1 :: [Int] -> Int
-- sumList1 = sum

-- -- ghc -O1 Fusion.hs -ddump-simpl -dsuppress-all -dno-suppress-type-signatures -dno-typeable-binds

-- -- SUCCESS
-- sumList2 :: [Int] -> Int
-- sumList2 xs = sum xs

-- -- SUCCESS
-- sumOfSquaresList :: [Int] -> Int
-- sumOfSquaresList = sum . map (\x -> x * x)

-- -- SUCCESS
-- sumOfSquaresList2 :: [Int] -> Int
-- sumOfSquaresList2 xs = sum $ map (\x -> x * x) xs

-- -- FAIL: the 3 maps are merged to one, but that last map is not inlined.
-- mapList :: [Int] -> [Int]
-- mapList xs = map (*1) $ map (*2) $ map (*3) xs

-- -- SUCCESS
-- sumMapList :: [Int] -> Int
-- sumMapList xs =
--   sum $
--   map (*1) $
--   map (*2) $
--   map (*3) $
--   xs

-- -- SUCCESS
-- filterList :: [Int] -> Int
-- filterList xs =
--   sum $
--   filter (< 1) $
--   filter (< 2) $
--   filter (< 3) $
--   xs

-- -- FAIL: creates intermediate list
-- dropList :: Int -> Int -> Int
-- dropList x y =
--   sum $
--   drop 100 $
--   map (+10) $
--   [x..y]

-- -- SUCCESS
-- cartList :: [Int] -> [Int] -> Int
-- cartList xs ys = sum $ liftM2 (*) xs ys

-- -- SUCCESS
-- bindTakeList :: [Int] -> [Int] -> Int
-- bindTakeList xs ys =
--   sum $
--   take 20000000 $
--   liftM2 (*) xs ys
