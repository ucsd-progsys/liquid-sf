{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Peano where

import Language.Haskell.Liquid.ProofCombinators

--------------------------------------------------------------------------------
-- | Peano Numbers -------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data Peano [toNat] = O | S Peano @-}
data Peano = O | S Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat O     = 0
toNat (S n) = 1 + toNat n

{-@ reflect plus @-}
plus :: Peano -> Peano -> Peano
plus O     n = n
plus (S m) n = S (plus m n)

{-@ reflect double @-}
double :: Peano -> Peano
double n = plus n n
