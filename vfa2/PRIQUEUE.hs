{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}
{-@ LIQUID "--exactdc"                             @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}

{-@ infix : @-}
{-@ infix ++ @-}

module PRIQUEUE where
import Prelude hiding(abs, (++), length)
import Language.Haskell.Liquid.ProofCombinators 
import qualified Language.Haskell.Liquid.Bag	as B
import qualified Data.Set as S 
import Permutations
import ThmForallPerm
import Lists
import Data.Maybe

-----------------------------------------------------------------------


data PRIQUEUE = P [Int] deriving (Ord, Eq)

{-* data PRIQUEUE [len] = P [Nat]*-}

{-@reflect priq@-}
{-@ priq:: l: PRIQUEUE -> {v:Bool | True} @-}
priq:: PRIQUEUE -> Bool
priq (P l) = True

{-@ reflect p_empty@-}
p_empty = P []

{-@reflect insert@-}
{-@insert ::  Nat -> PRIQUEUE -> PRIQUEUE @-}
insert :: Int -> PRIQUEUE -> PRIQUEUE 
insert x (P xs) = P (x:xs)

{-@reflect toList@-}
toList :: PRIQUEUE -> [Int]
toList (P l) = l 


{-@reflect merge@-}
{-@merge ::  PRIQUEUE -> PRIQUEUE -> PRIQUEUE @-}
merge :: PRIQUEUE -> PRIQUEUE -> PRIQUEUE 
merge (P xs) (P ys) = P (xs ++ ys)

data Pair a b = Pair a b  


{-@ measure snd1 @-}
snd1 :: (Pair a b) -> b 
snd1 (Pair _ x) = x


{-@ measure fst1 @-}
fst1 ::  (Pair a b) -> a 
fst1 (Pair x _) = x


{-@reflect first@-}
{-@ first:: p: {Maybe (Pair Int PRIQUEUE) | p/= Nothing} -> Int @-}
first:: Maybe (Pair Int PRIQUEUE) -> Int
first (Just (Pair a b)) = a


{-@reflect second@-}
{-@ second:: p: {Maybe (Pair Int PRIQUEUE) | p/= Nothing} -> PRIQUEUE @-}
second:: Maybe (Pair Int PRIQUEUE) -> PRIQUEUE
second (Just (Pair a b)) = b
 

{-@ reflect less_eq @-}
less_eq :: (Ord a) => a -> a -> Bool
less_eq x h = (x >= h)


{-@reflect delete_max@-}
{-@ delete_max :: p:PRIQUEUE -> p2 :{Maybe (Pair Int PRIQUEUE) |  p2/= Nothing ==> (permutation (toList p) ((first p2):(toList (second p2)))  )} @-} 
delete_max :: PRIQUEUE -> Maybe (Pair Int PRIQUEUE) 
delete_max (P []) = Nothing
delete_max (P (x:xs) ) = Just (Pair (fst1 y)  (P (snd1 y))) where y = select x xs


{-@ reflect select @-}
{-@ select :: (Ord a) => x:a -> l1: [a]  
           -> p: {(Pair  a [a]) | permutation (x:l1) (fst1 p : snd1 p) }@-}
select :: (Ord a) => a -> [a] -> (Pair a ([a]))
select i [] = (Pair i  [])
select i (x:xs) 
  | i >= x    = let (Pair j2 l2) = (select i xs) in (Pair j2 (x:l2))
  | otherwise = let (Pair j1 l1) = (select x xs) in (Pair j1 (i:l1))


{-@ thm_delete_max :: k:Int -> q:PRIQUEUE -> p: { PRIQUEUE | delete_max p =Just (Pair k q) } ->  { forall2 (less_eq k) (toList p) } @-}
thm_delete_max  :: Int -> PRIQUEUE -> PRIQUEUE-> Proof
thm_delete_max k q (P [])     = trivial
thm_delete_max k q (P (x:xs)) = undefined


{-@reflect abs@-}
{-@ abs:: l1: PRIQUEUE -> l2:[Nat] -> Bool @-}
abs:: PRIQUEUE -> [Int] -> Bool
abs (P l1) l2 = permutation l1 l2


{-@ abs_prop :: k:Nat -> q:{PRIQUEUE | forall2 (less_eq k) (toList q) } -> ql : {[Nat] | abs q ql}  -> { forall2 (less_eq k) ql} @-}
abs_prop :: Int -> PRIQUEUE -> [Int] -> Proof 
abs_prop k q ql = thm_Forall_perm (less_eq k) (toList q) ql

-----------------------------------------------------------------------


{-@ lemma_abs_perm :: p:PRIQUEUE -> al:{[Nat] | abs p al} -> bl:{[Nat] | abs p bl} -> { (permutation al bl)}@-}
lemma_abs_perm :: PRIQUEUE -> [Int] -> [Int] -> Proof
lemma_abs_perm p al bl = trivial


{-@ lemma_can_relate :: p:{PRIQUEUE | priq p} -> { abs p (toList p)}@-}
lemma_can_relate :: PRIQUEUE ->  Proof
lemma_can_relate p = trivial


{-@ lemma_empty_priq :: {priq p_empty}@-}
lemma_empty_priq:: Proof
lemma_empty_priq = trivial


{-@lemma_empty_relate :: {abs p_empty []}@-}       -- why abs p_empty [] doesn't work ??
lemma_empty_relate:: Proof
lemma_empty_relate = trivial


{-@ lemma_insert_priq:: p: {PRIQUEUE | priq p} -> k: Nat -> { priq (insert k p)} @-}
lemma_insert_priq:: PRIQUEUE -> Int -> Proof
lemma_insert_priq p k = trivial


{-@ lemma_insert_relate :: p: {PRIQUEUE | priq p} -> al: {[Nat]| abs  p al} -> k: Nat -> {abs (insert k p) (k:al)} @-}
lemma_insert_relate :: PRIQUEUE -> [Int] -> Int -> Proof
lemma_insert_relate p al k = trivial


{-@ lemma_merge_priq :: p: {PRIQUEUE | priq p} -> q: {PRIQUEUE | priq q} -> { priq (merge p q)} @-}
lemma_merge_priq :: PRIQUEUE -> PRIQUEUE -> Proof
lemma_merge_priq p q = trivial


{-@ lemma_delete_max_Some_priq :: p: {PRIQUEUE | priq p} -> k: Int -> q: {PRIQUEUE| (delete_max p = Just (Pair k q)) } -> {priq q} @-}
lemma_delete_max_Some_priq :: PRIQUEUE -> Int -> PRIQUEUE -> Proof
lemma_delete_max_Some_priq p k q = trivial



{-@ lemma_merge_relate :: p: {PRIQUEUE | priq p} -> q: {PRIQUEUE | priq q} -> pl: {[Nat] | abs p pl} -> ql: {[Nat] | abs q ql}
        -> al: {[Nat] | abs (merge p q) al} -> {permutation al (pl++ql)} @-}
lemma_merge_relate :: PRIQUEUE -> PRIQUEUE -> [Int] -> [Int] -> [Int] -> Proof
lemma_merge_relate p q pl ql al = [appendBag pl ql, appendBag (toList p) (toList q)] *** QED


{-@ lemma_delete_max_None_relate :: p: {PRIQUEUE | priq p}  -> { abs p [] <=> delete_max p == Nothing } @-}
lemma_delete_max_None_relate :: PRIQUEUE -> Proof
lemma_delete_max_None_relate (P [])    = trivial
lemma_delete_max_None_relate (P l)     = [thm_perm1 l] *** QED


{-@ lemma_delete_max_Some_relate :: q:PRIQUEUE -> k:Nat -> p: {PRIQUEUE | priq p && delete_max p = Just (Pair k q) }  
     -> pl: {[Nat] | abs p pl} -> ql: {[Nat] | abs q ql}  ->  {permutation pl (k:ql) && (forall2 (less_eq k) pl) } @-}
lemma_delete_max_Some_relate :: PRIQUEUE -> Int -> PRIQUEUE -> [Int] -> [Int] -> Proof
lemma_delete_max_Some_relate q k p pl ql = (delete_max p  ,permutation (toList p) (k:toList q),thm_delete_max k q p, abs_prop k p pl )*** QED


{-@ thm_perm1 :: xs: {[a] | len xs >0} ->  { permutation xs [] == False }  @-}
thm_perm1 :: (Eq a, Ord a) => [a] -> Proof 
thm_perm1 [] 
  = ()  
thm_perm1 (x:xs) 
  =   permutation xs [] 
  ==. bag xs == bag []
  ==. B.put x (bag xs) == B.empty 
       ? B.thm_emp x (bag xs)
  ==. False 
  *** QED 



