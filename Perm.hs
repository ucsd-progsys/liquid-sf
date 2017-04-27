
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{- LIQUID "--diff"                                @-}


module Perm where

import Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S

-- | Lists ---------------------------------------------------------------------

{-@ data List [llen] a = Nil | Cons {lHd :: a, lTl :: List} @-}
data List a = Nil | Cons a (List a)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons h t) = 1 + llen t

{-@ reflect app @-}
app :: List a -> List a -> List a
app Nil         ys = ys
app (Cons x xs) ys = Cons x (app xs ys)
--------------------------------------------------------------------------------

{-@ reflectExample2 ::a:Nat -> { (if a < 5 then a else 2) < 6 } @-}
reflectExample2 :: Int -> Proof
reflectExample2 a = trivial

{-@ omegaExample1 :: i:Nat -> j:Nat -> k:Nat ->
      {v:Proof | i < j} -> {v:Proof| not (k - 3 <= j)} ->
        { k > i }
  @-}
omegaExample1 :: Int -> Int -> Int -> Proof -> Proof -> Proof
omegaExample1 i j k _ _  = trivial

{-@ reflect maybeSwap @-}
maybeSwap :: (Ord a) => List a -> List a
maybeSwap (Cons a (Cons b ar)) = if a > b then Cons b (Cons a  ar) else (Cons a (Cons b ar))
maybeSwap ar                   = ar

{-@ testMaybeSwap123 :: { maybeSwap (Cons 1 (Cons 2 (Cons 3 Nil))) = Cons 1 (Cons 2 (Cons 3 Nil)) } @-}
testMaybeSwap123 = trivial

{-@ testMaybeSwap321 :: { maybeSwap (Cons 3 (Cons 2 (Cons 1 Nil))) = Cons 2 (Cons 3 (Cons 1 Nil)) } @-}
testMaybeSwap321 = trivial

thmMaybeSwapIdempotent :: (Ord a) => List a -> Proof

{-@ thmMaybeSwapIdempotent :: xs:List a ->
     { maybeSwap (maybeSwap xs) = maybeSwap xs }
  @-}
thmMaybeSwapIdempotent Nil                     = trivial
thmMaybeSwapIdempotent (Cons a2 Nil)           = trivial
thmMaybeSwapIdempotent (Cons a1 (Cons a2 as))
  | a1 < a2                                    = trivial
  | otherwise                                  = trivial


--------------------------------------------------------------------------------
-- | Permutations --------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ measure lElems @-}
lElems :: (Ord a) => List a -> S.Set a
lElems Nil         = S.empty
lElems (Cons x xs) = S.union (S.singleton x) (lElems xs)

{-@ reflect permutation @-}
permutation :: (Ord a) => List a -> List a -> Bool
permutation xs ys = lElems xs == lElems ys

{-@ exampleBut :: { permutation (Cons 1 (Cons 2 (Cons 3 Nil)))
                                (Cons 3 (Cons 2 (Cons 1 Nil))) } @-}
exampleBut = trivial

{-@ thmElemsApp :: xs:List a -> ys:List a ->
      { lElems (app xs ys) = S.union (lElems xs) (lElems ys) }
  @-}
thmElemsApp :: (Ord a) => List a -> List a -> Proof
thmElemsApp Nil ys         = trivial
thmElemsApp (Cons x xs) ys = thmElemsApp xs ys

{-@ thmPermutExample :: a:List Int -> b:List Int ->
      { permutation (Cons 5 (Cons 6 (app a b)))
                    (app (Cons 5 b) (app (Cons 6 a) Nil)) }
  @-}
thmPermutExample :: List Int -> List Int -> Proof
thmPermutExample a b
  = [ thmElemsApp a b
    , thmElemsApp (Cons 5 b) (Cons 6 a)
    , thmAppNilR (Cons 6 a)
    ] *** QED

{-@ thmAppNilR :: xs:List a -> { app xs Nil = xs } @-}
thmAppNilR :: List a -> Proof 
thmAppNilR Nil = trivial
thmAppNilR (Cons x xs) = thmAppNilR xs










{-

{-@ measure permutation :: List a -> List a -> Bool @-}

data Permutation a where

  PermNil  :: { permutation Nil Nil }

  PermSkip :: x:a -> l:List a -> l':List a -> { permutation l l' } ->
              { permutation (Cons x l) (Cons x l') }

  PermSwap :: x:a -> y:a -> l:List A ->
              { permutation (Cons x (Cons y l)) (Cons x (Cons y l)) }

  PermTrans :: l1:List a -> l2: List a -> l3:List a ->
              { permutation l1 l2 } -> {permutation l2 l3} ->
              { permutation l1 l3 }

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
    perm_nil : Permutation
  | perm_skip : forall (x : A) (l l' : list A),
                Permutation l l' ->
                Permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) (l : list A),
                Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall l l' l'' : list A,
                 Permutation l l' ->
                 Permutation l' l'' ->
                 Permutation l l''.

-}
