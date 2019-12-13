{-@ LIQUID "--exactdc"                             @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}


module SSort where
import Language.Haskell.Liquid.Bag	
import Language.Haskell.Liquid.ProofCombinators
import Permutations



{-@ infix : @-}


data Pair a b = Pair a b 


{-@ measure snd1 @-}
snd1 :: (Pair a b) -> b 
snd1 (Pair _ x) = x


{-@ measure fst1 @-}
fst1 ::  (Pair a b) -> a 
fst1 (Pair x _) = x


{-@ reflect all_greater_eq @-}
all_greater_eq :: (Ord a) => a -> a -> Bool
all_greater_eq x y = x <= y

{-@ thm_perm :: x: a -> y:a -> xs: [a] ->  ys: {[a]| permutation (x:xs) (y:ys) } -> i:a -> { permutation (x:(i:(xs)))  (y:(i:(ys))) } @-}
thm_perm:: a -> a -> [a] -> [a] -> a -> Proof
thm_perm x xs y ys i = trivial


{-@ thm_select_perm:: (Ord a) => x: a -> l: [a] -> { permutation (x:l) ((fst1 (select x l)) : (snd1 (select x l))) }  / [len l] @-}
thm_select_perm:: (Ord a) => a -> [a]  -> Proof  
thm_select_perm x []                  =   trivial
thm_select_perm x (l:ls)  | x <= l    =   permutation (x:(l:ls)) ((fst1 (select x (l:ls))) : (snd1 (select x (l:ls))))
                                       ==. permutation (x:(l:ls)) ((fst1 (select x ls)) : (l:(snd1 (select x ls))) )
                                       ==. True ? thm_select_perm x ls  &&& thm_perm x (fst1 (select x ls)) ls (snd1 (select x ls)) l
                                       *** QED 
thm_select_perm x (l:ls)  | x > l     =   permutation (x:(l:ls)) ((fst1 (select x (l:ls))) : (snd1 (select x (l:ls))))
                                       ==. permutation (x:(l:ls)) ((fst1 (select l ls)) : (x:(snd1 (select l ls))) )
                                       ==. True ? thm_select_perm l ls  &&& thm_perm l (fst1 (select l ls)) ls (snd1 (select l ls)) x
                                       *** QED 

{-@ reflect forall2 @-}
forall2 :: (a->Bool) -> [a] -> Bool
forall2 f []     = True
forall2 f (x:xs) = (f x) && (forall2 f xs)

{-@ reflect selSort @-}
{-@ selSort :: (Ord a) => xs:[a]  -> ys:[a]  @-}
selSort :: (Ord a) => [a]  -> [a] 
selSort []      = []
selSort (x:xs)  =  ((fst1 (select x xs)):selSort (snd1 (select x xs)))  


{-@ reflect select @-}
{-@ select :: (Ord a) => x:a -> l1: [a]  
           -> p: {(Pair  a [a]) |  (len l1 == len (snd1 p))  }@-}
select :: (Ord a) => a -> [a] -> (Pair a ([a]))
select i [] = (Pair i  [])
select i (x:xs) 
  | i <= x    = (Pair (fst1 (select i xs)) (x: (snd1 (select i xs)) ))
  | otherwise = (Pair (fst1 (select x xs)) (i:(snd1 (select x xs))))


{-@ thm_perm_aux :: xs:[a] -> ys:{[a] | permutation xs ys} -> zs:[a] -> { permutation xs zs <=> permutation ys zs}@-}
thm_perm_aux :: [a] -> [a] -> [a] -> Proof
thm_perm_aux xs ys zs = trivial

{-@ thm_selsort_perm:: (Ord a) => l: [a] ->  { permutation l (selSort l) } @-}
thm_selsort_perm:: (Ord a) => [a]  -> Proof
thm_selsort_perm []     = trivial
thm_selsort_perm (x:xs) =   permutation   (x:xs) (selSort (x:xs))
                        ==. permutation (x:xs) ((fst1 (select x xs)):selSort (snd1 (select x xs))) 
                        ==. permutation ((fst1 (select x xs)) : (snd1 (select x xs))) ((fst1 (select x xs)):selSort (snd1 (select x xs)))
                            ? thm_select_perm x xs &&& thm_perm_aux (x:xs) ((fst1 (select x xs)) : (snd1 (select x xs))) ((fst1 (select x xs)):selSort (snd1 (select x xs))) 
                        ==. True ? thm_selsort_perm  (snd1 (select x xs))
                        *** QED


{-@ reflect sorted1 @-}
sorted1 :: (Ord a) => a -> [a] -> Bool
sorted1 x []     = True
sorted1 x (y:ys) = if x <= y then sorted1 y ys else False


{-@ reflect sorted @-}
sorted :: (Ord a) => [a] -> Bool
sorted []        = True
sorted (h:t) = sorted1 h t

{-@ reflect lHd @-}
{-@ lHd :: (Ord a) => {v: [a] | len v > 0} -> a @-}
lHd :: (Ord a) => [a] -> a
lHd (x:_) = x

{-@ thm_3:: (Ord a) => x:a -> l:{[a] | forall2 (all_greater_eq x) l }  -> { forall2 (all_greater_eq x) (selSort l) } @-}
thm_3 :: (Ord a) => a -> [a] -> Proof
thm_3 x l = [thm_selsort_perm l, thm_Forall_perm (all_greater_eq x) l (selSort l)] *** QED


{-@ selection_sort_sorted_aux :: (Ord a) => bl :{ [a] | sorted (selSort bl) } -> y: {a | forall2 (all_greater_eq y) bl } 
         -> { sorted (y: selSort bl) } @-}
selection_sort_sorted_aux :: (Ord a) => [a] -> a -> Proof
selection_sort_sorted_aux [] y = trivial
selection_sort_sorted_aux bl y = (sorted (selSort bl), forall2 (all_greater_eq y) bl, ((thm_3 y bl) *** QED)) *** QED
     

{-@ selection_sort_sorted :: (Ord a) => l: [a]  -> { sorted (selSort l) } @-}
selection_sort_sorted :: (Ord a) => [a]  -> Proof
selection_sort_sorted []  = trivial
selection_sort_sorted (h:t) =   sorted (selSort (h:t))
                            ==. sorted ( ( (fst1 (select h t) ) :selSort (snd1 (select h t) ) ) )
                            ==. True  ? selection_sort_sorted (snd1 (select h t)) &&& (thm_select_smallest h t) &&& selection_sort_sorted_aux (snd1 (select h t)) (fst1 (select h t))
                            *** QED
   
{-@ thm_smallest_aux :: xs:[a] -> x:a -> { forall2 (all_greater_eq x) (x:xs) <=> forall2 (all_greater_eq x) xs } @-}
thm_smallest_aux :: [a] -> a -> Proof
thm_smallest_aux xs x = trivial

{-@ thm_Forall_perm :: f: (a -> Bool) -> al: [a] 
  -> bl: {[a] | permutation al bl} -> {  forall2 f al = forall2 f bl  } @-}
thm_Forall_perm :: Ord a => (a -> Bool) -> [a] -> [a] -> Proof

thm_Forall_perm f xs ys = undefined

{-@ thm_smallest_aux2 :: (Ord a) =>  x:a -> y:a ->  al: { [a] | forall2 (all_greater_eq y) (x:al) } -> {y<= x}  @-}
thm_smallest_aux2 :: (Ord a) => a -> a -> [a] -> Proof
thm_smallest_aux2 x y al = trivial

{-@ select_smallest_aux :: (Ord a) =>  x:a -> al:{[a] |forall2 (all_greater_eq (fst1 (select x al))) (snd1 (select x al)) } ->  { (fst1 (select x al)) <= x} @-}
select_smallest_aux :: (Ord a) => a -> [a] -> Proof
select_smallest_aux x al = ( thm_select_perm x al , thm_smallest_aux  ((fst1 (select x al)): (snd1 (select x al))) (fst1 (select x al)) , 
                          thm_Forall_perm ( all_greater_eq (fst1 (select x al)) ) (x:al) ((fst1 (select x al)) :(snd1 (select x al)) ), 
                          forall2 (all_greater_eq (fst1 (select x al)))  (x:al) ,thm_smallest_aux2  x (fst1 (select x al)) al ) *** QED  



{-@ thm_select_smallest :: (Ord a) => x:a -> xs:[a] ->  { forall2 (all_greater_eq (fst1 (select x xs))) (snd1 (select x xs)) } / [len xs] @-}
thm_select_smallest  :: (Ord a) => a -> [a] -> Proof
thm_select_smallest k [] = trivial
thm_select_smallest k (x:xs) | k <= x =   forall2 (all_greater_eq (fst1 (select x xs))) (snd1 (select x xs))
                                      ==. forall2 (all_greater_eq (fst1 (select k xs))) (x:snd1 (select k xs))
                                      ==. True ?  thm_select_smallest k xs &&& select_smallest_aux k xs
                                      *** QED

thm_select_smallest k (x:xs) | k > x = forall2 (all_greater_eq (fst1 (select x xs))) (snd1 (select x xs))
                                      ==. forall2 (all_greater_eq (fst1 (select x xs))) (k:snd1 (select x xs))
                                      ==. True ?  thm_select_smallest x xs &&& select_smallest_aux x xs
                                      *** QED
    
