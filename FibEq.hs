{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module FibEq where

import Language.Haskell.Liquid.Prelude (liquidAssert)
import Prelude hiding (sum)

{-@ reflect fib @-}
{-@ fib :: a -> n:Nat -> Nat / [n] @-}
fib   :: a -> Int -> Int
fib x n = if n <= 1 then 1 else fib x (n-2) + fib x (n-1)

-- 0, 1, 2, 3, 4, 5,  6,  7, 8,  9,  10
-- 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89

{-@ test :: {fib 0 7 == 21} @-}
test :: ()
test = ()

{-@ zink :: {v:Int | v == 8} @-}
zink = foo 5
  where
    foo = \a -> liquidAssert (fib 0 a == 8) (fib 0 a)

{-@ reflect sum @-}
sum :: [Int] -> Int
sum []     = 0
sum (x:xs) = x + sum xs

{-@ goo :: {v:Int | v == 6} @-}
goo = f 2
  where
    f = \x -> let t = sum [x, x, x] in
                liquidAssert (t == 6) t


{-@ reflect incr @-}
{-@ incr :: Nat -> Int -> Int @-}
incr :: Int -> Int -> Int
incr n x = if n == 0 then x + 1 else incr (n - 1) x

{-@ propIncr :: y:Int -> { incr 10 y == y + 1 } @-} -- 1 + incr 0 (y - 1) } @-}
propIncr :: Int -> ()
propIncr y = ()
