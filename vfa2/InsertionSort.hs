{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}

module ISort where  

import qualified Language.Haskell.Liquid.Bag as B
import Language.Haskell.Liquid.ProofCombinators
import Permutations


{-@ infix : @-}

{-@ reflect insert2 @-}
insert2 :: (Ord a) => a -> [a] -> [a]
insert2 i []    =  [i]
insert2 i (x:xs)  
	 | i <= x     = (i:(x:xs)) 
	 | otherwise  = (x:(insert2 i xs))	


{-@ reflect sort@-}
sort :: (Ord a) => [a] -> [a]
sort []     = []
sort (x:xs) = insert2 x (sort xs)


{-@ thmInsertPerm :: (Ord a) => x:a -> xs:[a] ->
      { permutation (x:xs) (insert2 x xs) }
  @-}
thmInsertPerm :: (Ord a) => a -> [a] -> Proof
thmInsertPerm x [] = trivial
thmInsertPerm x (h:t)
  | x <= h    = trivial
  | otherwise = thmInsertPerm x t


{-@ thmSortPerm :: (Ord a) => xs: [a] -> { permutation xs (sort xs) } @-}
thmSortPerm :: (Ord a) => [a] -> Proof
thmSortPerm []     = trivial
thmSortPerm (x:xs) = [ thmSortPerm xs, thmInsertPerm x (sort xs) ] *** QED





{-@ reflect sorted1 @-}
sorted1 :: (Ord a) => a -> [a] -> Bool
sorted1 x []     = True
sorted1 x (y:ys) = if x <= y then sorted1 y ys else False


{-@ reflect sorted @-}
sorted :: (Ord a) => [a] -> Bool
sorted []        = True
sorted (h:t) = sorted1 h t





{-@ thmInsertSorted :: x:a -> ys:{[a] | sorted ys} -> { sorted (insert2 x ys) } @-}
thmInsertSorted :: (Ord a) => a -> [a] -> Proof
thmInsertSorted x []        =   trivial
thmInsertSorted x [h]       
	 | x <= h =  trivial
	 | x > h =  trivial
thmInsertSorted x (h:(y:t)) 
     | x <= h               =   trivial
     | x > h && x <= y      =   trivial 
     | x > h && x > y       =   thmInsertSorted x (y:t)
                            


{-@ thmSortSorted :: xs: [a] -> { sorted (sort xs) } @-}
thmSortSorted :: (Ord a) => [a] -> Proof
thmSortSorted []         = trivial
thmSortSorted (x:xs)     = [thmSortSorted xs, thmInsertSorted x (sort xs) ] *** QED
