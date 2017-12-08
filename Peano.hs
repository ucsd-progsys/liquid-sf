{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

module Peano where

import Language.Haskell.Liquid.NewProofCombinators

--------------------------------------------------------------------------------
-- | Peano Numbers -------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data Peano [toNat] @-}
data Peano where
  Z :: Peano
  S :: Peano -> Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat Z     = 0
toNat (S n) = 1 + toNat n

{-@ reflect prev @-}
prev :: Peano -> Peano
prev Z     = Z
prev (S n) = n

{-@ reflect plus @-}
plus :: Peano -> Peano -> Peano
plus Z     n = n
plus (S m) n = S (plus m n)

{-@ reflect double @-}
double :: Peano -> Peano
double n = plus n n

{-@ plus_zero_r :: n:Peano -> { plus n Z = n } @-}
plus_zero_r :: Peano -> ()
plus_zero_r Z     = ()
plus_zero_r (S n) = plus_zero_r n

{-@ plus_succ_r :: n:Peano -> m:Peano -> { plus n (S m) = S (plus n m)} @-}
plus_succ_r :: Peano -> Peano -> ()
plus_succ_r Z     m = ()
plus_succ_r (S n) m = plus_succ_r n m

{-@ plus_comm :: n:Peano -> m:Peano -> { plus n m = plus m n } @-}
plus_comm :: Peano -> Peano -> ()
plus_comm Z     m = plus_zero_r m
plus_comm (S n) m = plus_comm n m &&& plus_succ_r (S m) n

{-@ plus_assoc :: n:Peano -> m:Peano -> p:Peano ->
    { plus (plus n m) p = plus n (plus m p) } @-}
plus_assoc :: Peano -> Peano -> Peano -> ()
plus_assoc Z m p     = ()
plus_assoc (S n) m p = plus_assoc n m p
