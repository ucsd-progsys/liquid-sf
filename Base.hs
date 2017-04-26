
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{- LIQUID "--diff"                                @-}

module Base where

import Language.Haskell.Liquid.ProofCombinators

--------------------------------------------------------------------------------

{-@ data Peano [toNat] = O | S Peano @-}
data Peano = O | S Peano

{-@ measure toNat @-}
{-@ toNat :: Peano -> Nat @-}
toNat :: Peano -> Int
toNat O     = 0
toNat (S n) = 1 Prelude.+ toNat n

{-@ reflect plus @-}
plus :: Peano -> Peano -> Peano
plus O     n = n
plus (S m) n = S (plus m n)

-- | Pairs ---------------------------------------------------------------------

{-@ data Pair a b = Pair { px :: a, py :: b} @-}
data Pair a b = Pair a b

{-@ measure pFst @-}
pFst :: Pair a b -> a
pFst (Pair x y) = x

{-@ measure pSnd @-}
pSnd :: Pair a b -> b
pSnd (Pair x y) = y

-- | Lists ---------------------------------------------------------------------

{-@ data List [llen] a = Nil | Cons {lHd :: a, lTl :: List} @-}
data List a = Nil | Cons a (List a)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons h t) = 1 Prelude.+ llen t

-- | Append---------------------------------------------------------------------

{-@ reflect app @-}
app :: List a -> List a -> List a
app Nil         ys = ys
app (Cons x xs) ys = Cons x (app xs ys)

{-@ reflect rev @-}
rev :: List a -> List a
rev Nil         = Nil
rev (Cons x xs) = app (rev xs) (Cons x Nil)

-- | Options -------------------------------------------------------------------

{-@ data Option a = None | Some a @-}
data Option a = None | Some a

-- | Partial Maps -------------------------------------------------------------

type Key = Int
type Val = Int

{-@ data Map [mlen] k v = Empty | Record {mKey :: k, mVal :: v, mRest :: Map k v } @-}
data Map k v
  = Empty
  | Record k v (Map k v)

{-@ measure mlen @-}
{-@ mlen :: Map k v -> Nat @-}
mlen :: Map k v -> Int
mlen Empty          = 0
mlen (Record k v r) = 1 + (mlen r)

{-@ reflect update @-}
update :: Map k v -> k -> v -> Map k v
update m k v = Record k v m

{-@ reflect find @-}
find :: (Eq k) => Map k v -> k -> Option v
find Empty          key = None
find (Record k v r) key
  | k == key            = Some v
  | otherwise           = find r key
