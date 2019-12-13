{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module ThmForallPerm where 
 
import qualified Language.Haskell.Liquid.Bag as B
import Language.Haskell.Liquid.ProofCombinators
import Lists
import Permutations
import Prelude hiding ((++))

import qualified Data.Set as S 

{-@ infix   ++ @-}
{-@ infix   : @-}


{-@ reflect forall2 @-}
forall2 :: (a->Bool) -> [a] -> Bool
forall2 f []     = True
forall2 f (x:xs) = (f x) && (forall2 f xs)

{-@ thm_emp_bag :: Ord k => x:k -> xs:B.Bag k 
   ->  { B.empty /= B.put x xs } @-}
thm_emp_bag :: Ord k => k -> B.Bag k -> () 
thm_emp_bag x xs  = B.get x xs  *** QED 

 
{-@ elemForAllExists :: f:(a -> Bool) -> xs:{[a] | not (forall2 f xs)} 
     -> (x::a, {v:() | S.member x (listElts xs) && (not (f x))}) @-} 
elemForAllExists :: (a -> Bool) -> [a] -> (a,()) 
elemForAllExists f (x:xs)
  | not (forall2 f (x:xs)) 
  = if f x then elemForAllExists f xs else (x,())

elemToBagMember :: Ord a => a -> [a] -> ()
{-@ elemToBagMember :: x:a -> xs:{[a] | S.member x (listElts xs)} 
     -> {1 <= B.get x (bag xs) } @-}
elemToBagMember x []     = ()
elemToBagMember x (y:ys) 
  | x == y
  =   B.get x (bag (y:ys)) 
  ==. B.get x (B.put y (bag ys))
  ==. 1 + B.get x (bag ys)
  *** QED   
  | x /= y
  =   B.get x (bag (y:ys)) 
  ==. B.get x (B.put y (bag ys))
  ==. B.get x (bag ys)
       ? elemToBagMember x ys 
  *** QED


bagMember :: Ord a => a -> [a] -> ()
{-@ bagMember :: x:a -> xs:[a] 
     -> {S.member x (listElts xs) <=> (1 <= B.get x (bag xs))} @-}
bagMember x []     = ()
bagMember x (y:ys)
  |  not (S.member x (S.fromList (y:ys)))
  = bagMember x ys 
  |  not (1 <= B.get x (bag (y:ys)))
  = elemToBagMember x (y:ys) &&& bagMember x ys 
  | otherwise
  = ()

{-@ assert :: b:{Bool | b } -> { b } @-} 
assert :: Bool -> () 
assert _ = () 

{-@ permutationsElem :: x:a -> ys:[a] -> xs:{[a] | permutation xs ys } 
  -> {  S.member x (listElts xs) <=> S.member x (listElts ys) } @-}
permutationsElem :: Ord a => a -> [a] -> [a] -> () 
permutationsElem x ys xs 
  =   assert (permutation xs ys)
  &&& (bagMember x xs) 
  &&& (bagMember x ys) 


{-@ elemForAll :: f:(a -> Bool) -> x:{a | not (f x) } 
  -> xs:{[a] | S.member x (listElts xs) } 
  -> { not (forall2 f xs) } @-} 
elemForAll :: Ord a => (a -> Bool) -> a -> [a] -> () 
elemForAll f x [] 
  = S.member x (S.fromList []) *** QED  
elemForAll f y (x:xs)
  | y == x 
  =   forall2 f (x:xs) 
  ==. (f x && forall2 f xs) 
  ==. False 
  *** QED  
  | otherwise
  =   forall2 f (x:xs)
  ==. (f x && forall2 f xs)
      ? elemForAll f y xs 
  ==. False 
  *** QED 


{-@ thm_Forall_perm :: f: (a -> Bool) -> al: [a] 
  -> bl: {[a] | permutation al bl} -> {  forall2 f al = forall2 f bl  } @-}
thm_Forall_perm :: Ord a => (a -> Bool) -> [a] -> [a] -> Proof

thm_Forall_perm f xs ys 
  | forall2 f xs && not (forall2 f ys) 
  = case elemForAllExists f ys of 
  	  (y, pf) -> permutationsElem y xs ys 
  	          &&& elemForAll f y xs 
  | not (forall2 f xs) && forall2 f ys
  = case elemForAllExists f xs of 
  	  (x, pf) -> permutationsElem x xs ys 
  	          &&& elemForAll f x ys 
  | otherwise 
  = () 


