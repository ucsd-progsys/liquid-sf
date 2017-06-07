{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module FibEq where

{-@ reflect incr @-}
{-@ incr :: Nat -> Int -> Int @-}
incr :: Int -> Int -> Int
incr n x = if n == 0 then x + 1 else incr (n - 1) x

{-@ propIncr :: y:Int -> { incr 25 y == y + 1 } @-}
propIncr :: Int -> ()
propIncr y = ()
