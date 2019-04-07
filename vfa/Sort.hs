{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}

module Sort where

import Prelude hiding ((++))
import ProofCombinators
import Lists
import Perm 

-- | Insertion Sort ------------------------------------------------------------

{-@ reflect sort @-}
sort :: (Ord a) => [a] -> [a]
sort []    = [] 
sort (h:t) = insert h (sort t)

{-@ reflect insert @-}
insert :: (Ord a) => a -> [a] -> [a]
insert x []    = [x] 
insert x (h:t)
  | x <= h     = x : h : t
  | otherwise  = h : insert x t

{-@ reflect foldRight @-}
foldRight :: (a -> b -> b) -> b -> [a] -> b
foldRight f b []     = b
foldRight f b (x:xs) = f x (foldRight f b xs)

{-@ reflect isort @-}
isort :: (Ord a) => [a] -> [a]
isort xs = foldRight insert [] xs

{-@ testSort :: _ -> TT @-} 
testSort _ = isort [3,1,2] == [1,2,3] 

-- | Specification of Sortedness ----------------------------------------------

{-@ reflect sorted @-}
sorted :: (Ord a) => [a] -> Bool
sorted []       = True
sorted [x]      = True
sorted (x:y:zs) = x <= y && sorted (y:zs)

-- | Proof of Correctness ---------------------------------------------------------

{-@ thm_insert_perm :: (Ord a) => x:_ -> xs:_ -> { perm (cons x xs) (insert x xs) }
  @-}
thm_insert_perm :: (Ord a) => a -> [a] -> Proof
thm_insert_perm x (h:t)
  | x <= h           = () 
  | otherwise        = thm_insert_perm x t
thm_insert_perm _ [] = () 

{-@ thm_sort_perm :: (Ord a) => xs:_ -> { perm xs (sort xs) } @-}
thm_sort_perm :: (Ord a) => [a] -> Proof
thm_sort_perm []     = () 
thm_sort_perm (x:xs) = () ? thm_sort_perm xs ? thm_insert_perm x (sort xs)

{-@ lem_ins :: h:_ -> x:{h < x} -> t:{sorted (cons h t)} -> {sorted (cons h (insert x t))} @-}
lem_ins :: (Ord a) => a -> a -> [a] -> Proof 
lem_ins _ _ []     = () 
lem_ins h x (y:ys) 
  | x <= y         = () 
  | otherwise      = lem_ins y x ys 

{-@ lem_ins_sorted :: x:_ -> ys:{sorted ys} -> { sorted (insert x ys) } @-}
lem_ins_sorted :: (Ord a) => a -> [a] -> Proof
lem_ins_sorted x []   = () 
lem_ins_sorted x (h:t)
  | x <= h            = ()
  | otherwise         = () ? lem_ins h x t 

{-@ thm_sort_sorted :: xs:_ -> { sorted (sort xs) } @-}
thm_sort_sorted :: (Ord a) => [a] -> Proof
thm_sort_sorted []     = () 
thm_sort_sorted (x:xs) = thm_sort_sorted xs &&& lem_ins_sorted x (sort xs)

-- | Specification of Correctness --------------------------------------------

{-@ type Is_Sorting_Algo F = xs:_ -> { perm xs (F xs) && sorted (F xs) } @-}

-- | Verification of Correctness --------------------------------------------

{-@ thm_sort_correct :: Is_Sorting_Algo sort @-}
thm_sort_correct :: (Ord a) => [a] -> Proof 
thm_sort_correct xs = thm_sort_sorted xs &&& thm_sort_perm xs

{-# ANN module "HLint: ignore Use camelCase" #-}