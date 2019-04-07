{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}

module Perm where

import Lists
import ProofCombinators
import qualified Data.Set as S
import Prelude hiding ((++))

-- | Omega -------------------------------------------------------------------

{-@ thm_omega_example1 :: i:_ -> j:_ -> k:_ -> { i < j => (k - 3 > j) => k > i } @-}
thm_omega_example1 :: Int -> Int -> Int -> Proof
thm_omega_example1 _ _ _ = ()

-- | Maybe-Swap --------------------------------------------------------------

{-@ reflect maybeSwap @-}
maybeSwap :: (Ord a) => [a] -> [a]
maybeSwap (a : b : ar) = if a > b then b : a : ar else (a : b : ar)
maybeSwap ar           = ar

{-@ testMaybeSwap123 :: _ -> TT @-}
testMaybeSwap123 _ = maybeSwap [1, 2, 3] == [1, 2, 3]

{-@ testMaybeSwap321 :: _ -> TT @-}
testMaybeSwap321 _ = maybeSwap [3, 2, 1] == [2, 3, 1]

{-@ thm_maybe_swap_idemp :: xs:_ -> { maybeSwap (maybeSwap xs) = maybeSwap xs } @-}
thm_maybe_swap_idemp :: (Ord a) => [a] -> Proof
thm_maybe_swap_idemp (a1:a2:as) 
  | a1 < a2              = () 
  | otherwise            = () 
thm_maybe_swap_idemp [_] = ()
thm_maybe_swap_idemp []  = ()

-- | Permutations --------------------------------------------------------------

{-@ measure lElems @-}
lElems :: (Ord a) => [a] -> S.Set a
lElems []     = S.empty
lElems (x:xs) = S.union (S.singleton x) (lElems xs)

{-@ reflect perm @-}
perm :: (Ord a) => [a] -> [a] -> Bool
perm xs ys = lElems xs == lElems ys

{-@ exampleBut :: _ -> TT @-} 
exampleBut _ =  perm [1,2,3] [3,2,1] 

{-@ ex_not_perm :: _ -> FF @-}
ex_not_perm _ = perm [1,1] [1,2]

{-@ thm_perm_examples :: a:_ -> b:_ -> 
      { perm (cons 5 (cons 6 (a ++ b))) ((cons 5 b) ++ (cons 6 a)) }
  @-}
thm_perm_examples :: [Int] -> [Int] -> Proof
thm_perm_examples a b
  = () ? thm_elems_app a b
       ? thm_elems_app (5:b) (6:a)

{-@ thm_elems_app :: xs:_ -> ys:_ ->
      { lElems (xs ++ ys) = S.union (lElems xs) (lElems ys) }
  @-}
thm_elems_app :: (Ord a) => [a] -> [a] -> () 
thm_elems_app []     ys = () 
thm_elems_app (x:xs) ys = thm_elems_app xs ys

{-@ thm_maybe_swap_perm :: xs:_ -> { perm xs (maybeSwap xs) } @-}
thm_maybe_swap_perm :: (Ord a) => [a] -> Proof 
thm_maybe_swap_perm (a1:a2:as) 
  | a1 < a2             = ()
  | otherwise           = ()
thm_maybe_swap_perm [_] = ()
thm_maybe_swap_perm []  = ()

-- | Correctness of `maybeSwap` ---------------------------------------------------------

{-@ reflect fst_le_snd @-}
fst_le_snd :: (Ord a) => [a] -> Bool 
fst_le_snd (x:y:_) = x <= y 
fst_le_snd _       = True 

{-@ thm_maybe_swap_fle :: xs:_ -> { fst_le_snd (maybeSwap xs) } @-}
thm_maybe_swap_fle :: (Ord a) => [a] -> Proof 
thm_maybe_swap_fle (a1:a2:as) 
  | a1 < a2            = ()
  | otherwise          = ()
thm_maybe_swap_fle [_] = ()
thm_maybe_swap_fle []  = ()

{-@ thm_maybe_swap_correct :: xs:_ -> { perm xs (maybeSwap xs) && fst_le_snd (maybeSwap xs) }  @-}
thm_maybe_swap_correct :: (Ord a) => [a] -> Proof 
thm_maybe_swap_correct xs = thm_maybe_swap_perm xs &&& thm_maybe_swap_fle xs 


-- | Properties of Permutations ------------------------------------------------

{-@ type All Xs P = xall1:{ S.member xall1 (lElems Xs) } -> {P xall1} @-}

{-@ thm_perm_prop :: p:_ -> xs:_ -> ys:{perm xs ys} -> (All xs p) -> (All ys p) @-}
thm_perm_prop :: (Ord a) => (a -> Bool) -> [a] -> [a] -> (a -> Proof) -> a -> Proof
thm_perm_prop _ _ _ pf = pf 