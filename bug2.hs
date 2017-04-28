
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--no-termination"                      @-}

module Sort where

import Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S

-- | Lists ---------------------------------------------------------------------

{-@ data List a <p :: xh:a -> a -> Bool> = Nil | Cons {lHd :: a, lTl :: List <p> (a <p lHd>) } @-}
data List a = Nil | Cons a (List a)

-- | Insertion Sort ------------------------------------------------------------

{-@ type OList a = List <{\h v -> h <= v}> a @-}

{-@ reflect sort @-}
{-@ sort :: (Ord a) => List a -> OList a @-}
sort :: (Ord a) => List a -> List a
sort Nil        = Nil
sort (Cons h t) = insert h (sort t)

{-@ reflect insert @-}
{-@ insert :: (Ord a) => a -> OList a -> OList a @-}
insert :: (Ord a) => a -> List a -> List a
insert x Nil        = Cons x Nil
insert x (Cons h t)
  | x <= h          = Cons x (Cons h t)
  | otherwise       = Cons h (insert x t)

{-@ reflect sorted @-}
sorted :: (Ord a) => List a -> Bool
sorted Nil
  = True
sorted (Cons h Nil)
  = True
sorted (Cons x1 (Cons x2 t))
  = if x1 <= x2
      then sorted (Cons x2 t)
      else False

{-@ thmOListSorted :: (Ord a) => xs:OList a -> { sorted xs } @-}
thmOListSorted :: (Ord a) => List a -> Proof
thmOListSorted Nil                     = trivial
thmOListSorted (Cons h Nil)            = trivial
thmOListSorted (Cons x1 (Cons x2 Nil)) = trivial
