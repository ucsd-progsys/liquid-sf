{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Permutations where 

import qualified Language.Haskell.Liquid.Bag as B
import Language.Haskell.Liquid.ProofCombinators
import Lists
import Prelude hiding ((++))


{-@ infix   ++ @-}
{-@ infix   :  @-}


{-@ measure bag @-}
bag :: (Ord a) => [a] -> B.Bag a
bag []     = B.empty
bag (x:xs) = B.put x (bag xs)

{-@ appendBag :: (Eq k, Ord k) => as:[k] -> bs:[k] -> { (bag (as ++ bs)) == (B.union (bag as) (bag bs)) } @-}
appendBag :: (Eq k, Ord k) => [k] -> [k] -> Proof
appendBag [] _      = ()       
appendBag (_:as) bs = appendBag as bs


{-@ reflect permutation @-}
permutation :: Ord a => [a] -> [a] -> Bool
permutation xs ys = (bag xs == bag ys )



{-@ exampleBut :: { permutation (1:(2:(3:[]))) (3:(2:(1:[]))) } @-}
exampleBut :: Proof
exampleBut = trivial


{-@ exNotPermutation :: { not (permutation (1:(1:[])) (1:(2:[]))) } @-}
exNotPermutation = trivial


{-@ thmPermProp2 :: x:_ -> y:_ -> xs:_ -> {permutation (x:(y:xs)) (y:(x:xs))} @-}
thmPermProp2:: (Ord a) => a -> a -> [a] -> Proof
thmPermProp2 x y []     = trivial
thmPermProp2 x y (_:xs) = thmPermProp2 x y xs

{-@ thmPermProp1 :: xs:_ -> {permutation xs xs} @-}
thmPermProp1:: (Ord a) => [a] -> Proof
thmPermProp1 []     = trivial 
thmPermProp1 (_:xs) = thmPermProp1 xs

{-@ thmPermProp3 :: x:a -> ys:[a] -> xs:{[a] | permutation xs ys} ->  {permutation (x:xs) (x:ys)} @-}
thmPermProp3:: (Ord a) => a -> [a] -> [a] -> Proof
thmPermProp3 x xs ys = trivial


{-@ permut_example :: a:_ -> b:_ -> {permutation (5:(6:(a ++ b))) ((5:b) ++ ((6:a) ++ [])) } @-}
permut_example :: [Int] -> [Int] -> Proof
permut_example as bs = [ appendBag as bs, lemma_app_Nil2 (6:as), appendBag (5:bs) ((6:as) ++ [])] *** QED


{-@ reflect maybeSwap @-}
maybeSwap :: Ord a => [a] -> [a]
maybeSwap (a:(b:ar)) = if a > b then b:(a:ar) else (a:(b:ar))
maybeSwap ar         = ar


{-@ reflect fstLeSnd @-}
fstLeSnd :: (Ord a) => [a] -> Bool
fstLeSnd (a1:(a2:as)) = a1 <= a2
fstLeSnd as = True


{-@ testMaybeSwap123 :: { maybeSwap (1:(2:(3:[]))) = (1:(2:(3:[]))) } @-}
testMaybeSwap123 :: Proof
testMaybeSwap123 = trivial


{-@ testMaybeSwap321 :: { maybeSwap (3:(2:(1:[]))) = (2:(3:(1:[]))) } @-}
testMaybeSwap321 :: Proof
testMaybeSwap321 = trivial

{-@ maybe_swap_idempotent :: xs: [a] -> { maybeSwap (maybeSwap xs) = maybeSwap xs } @-}
maybe_swap_idempotent :: (Ord a) => [a] -> Proof
maybe_swap_idempotent []       = trivial
maybe_swap_idempotent [x]      = trivial                        
maybe_swap_idempotent (x:y:xs) = trivial


{-@ thmMaybeSwap12 :: xs:_ -> { fstLeSnd (maybeSwap xs) } @-}
thmMaybeSwap12 :: (Ord a) => [a] -> Proof
thmMaybeSwap12 []           = trivial
thmMaybeSwap12 [a1]         = trivial
thmMaybeSwap12 (a1:(a2:as))
	| a1 < a2               = trivial
	| otherwise             = trivial


{-@ maybe_swap_perm :: xs:_ -> {permutation xs (maybeSwap xs)} @-}
maybe_swap_perm:: (Ord a) => [a]-> Proof
maybe_swap_perm []      = trivial 
maybe_swap_perm [_]     = trivial 
maybe_swap_perm(_:_:_) = trivial

{-@ thm_maybe_swap_correct :: xs:_ -> { permutation xs (maybeSwap xs) && fstLeSnd (maybeSwap xs) }  @-}
thm_maybe_swap_correct :: (Ord a) => [a] -> Proof 
thm_maybe_swap_correct xs = maybe_swap_perm xs &&& thmMaybeSwap12 xs 

-- | Properties of Permutations ------------------------------------------------


{-@ type All Xs P = xall1:{ (B.get xall1 (bag Xs)) > 0 } -> {P xall1} @-}

{-@ thm_perm_prop :: p:_ -> xs:_ -> ys:{permutation xs ys} -> (All xs p) -> (All ys p) @-}
thm_perm_prop :: (Ord a) => (a -> Bool) -> [a] -> [a] -> (a -> Proof) -> a -> Proof
thm_perm_prop _ _ _ pf = pf 

