module Blank where


{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}

import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect fib @-}
{-@ fib :: Nat -> Nat @-}
fib :: Int -> Int
fib n = if n == 0
          then 1
          else if n == 1
                 then 1
                 else fib (n-1) + fib(n-2)

{-@ fibUp :: i:Nat -> {fib i <= fib (i + 1)} @-}
fibUp :: Int -> Proof
fibUp 0 = trivial
fibUp 1 = trivial
fibUp n = fib n + fib (n-1) ==. fib (n + 1) *** QED
