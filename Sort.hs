
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{- LIQUID "--diff"                                @-}

module Sort where

import Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S

-- | Lists ---------------------------------------------------------------------

{-@ data List [llen] a = Nil | Cons {lHd :: a, lTl :: List a} @-}
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


{-@ reflect maybeSwap @-}
maybeSwap :: (Ord a) => List a -> List a
maybeSwap (Cons a (Cons b ar)) = if a > b then Cons b (Cons a  ar) else (Cons a (Cons b ar))
maybeSwap ar                   = ar

-- thmMaybeSwapIdempotent :: (Ord a) => List a -> Proof

{-@ thmMaybeSwapIdempotent :: xs:List a ->
     { maybeSwap (maybeSwap xs) = maybeSwap xs }
  @-}
thmMaybeSwapIdempotent Nil                     = trivial
thmMaybeSwapIdempotent (Cons a2 Nil)           = trivial
thmMaybeSwapIdempotent (Cons a1 (Cons a2 as))
  | a1 < a2                                    = trivial
  | otherwise                                  = trivial

-- | Permutations --------------------------------------------------------------

{-@ measure lElems @-}
lElems :: (Ord a) => List a -> S.Set a
lElems Nil         = S.empty
lElems (Cons x xs) = S.union (S.singleton x) (lElems xs)

{-@ reflect permutation @-}
permutation :: (Ord a) => List a -> List a -> Bool
permutation xs ys = lElems xs == lElems ys

-- HACK
{-@ inline perm @-}
perm :: (Ord a) => List a -> List a -> Bool
perm xs ys = lElems xs == lElems ys

{-@ thmElemsApp :: xs:List a -> ys:List a ->
      { lElems (app xs ys) = S.union (lElems xs) (lElems ys) }
  @-}
thmElemsApp :: (Ord a) => List a -> List a -> Proof
thmElemsApp Nil ys         = trivial
thmElemsApp (Cons x xs) ys = thmElemsApp xs ys

{-@ thmAppNilR :: xs:List a -> { app xs Nil = xs } @-}
thmAppNilR :: List a -> Proof
thmAppNilR Nil = trivial
thmAppNilR (Cons x xs) = thmAppNilR xs




-- | Insertion Sort ------------------------------------------------------------


-- This works automatically too.
{- insert :: (Ord a) => x:a -> xs:List a -> {v:List a | permutation (Cons x xs) v} @-}


{-@ reflect sort @-}
sort :: (Ord a) => List a -> List a
sort Nil        = Nil
sort (Cons h t) = insert h (sort t)

{-@ reflect insert @-}
insert :: (Ord a) => a -> List a -> List a
insert x Nil        = Cons x Nil
insert x (Cons h t)
  | x <= h          = Cons x (Cons h t)
  | otherwise       = Cons h (insert x t)

{-@ reflect foldRight @-}
foldRight :: (a -> b -> b) -> b -> List a -> b
foldRight f b Nil         = b
foldRight f b (Cons x xs) = f x (foldRight f b xs)

{-@ reflect isort @-}
isort :: (Ord a) => List a -> List a
isort xs = foldRight insert Nil xs

{-@ testSort :: { isort (Cons 3 (Cons 1 (Cons 2 Nil)))
                      =  Cons 1 (Cons 2 (Cons 3 Nil)) } @-}
testSort = trivial

---

{-@ thmInsertPerm :: (Ord a) => x:a -> xs:List a ->
      { permutation (Cons x xs) (insert x xs) }
  @-}
thmInsertPerm :: (Ord a) => a -> List a -> Proof
thmInsertPerm _ Nil        = trivial
thmInsertPerm x (Cons h t)
  | x <= h                 = trivial
  | otherwise              = thmInsertPerm x t

{-@ thmSortPerm :: (Ord a) => xs:List a -> { permutation xs (sort xs) } @-}
thmSortPerm :: (Ord a) => List a -> Proof
thmSortPerm Nil         = trivial
thmSortPerm (Cons x xs) = [ thmSortPerm xs, thmInsertPerm x (sort xs) ] *** QED

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

{-@ thmInsertSorted :: x:a -> ys:{List a | sorted ys} -> { sorted (insert x ys) } @-}
thmInsertSorted :: (Ord a) => a -> List a -> Proof
thmInsertSorted = undefined

-- thmInsertSorted x Nil         = trivial
-- thmInsertSorted x (Cons y ys)
  -- | x <= y                    = trivial
  -- | otherwise                 = thmInsertSorted x ys
 
{-@ thmSortSorted :: xs:List a -> { sorted (sort xs) } @-}
thmSortSorted :: (Ord a) => List a -> Proof
thmSortSorted Nil         = trivial
thmSortSorted (Cons x xs) = [ thmSortSorted xs, thmInsertSorted x xs ] *** QED







----
