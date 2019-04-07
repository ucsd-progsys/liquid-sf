{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--diff"       @-}
{-@ infixr ++             @-}

module Selection where



import Lists
import Perm
import Sort
import ProofCombinators
import qualified Data.Set as S
import Prelude hiding (fst, snd, (++))

{-@ reflect fst @-}
fst :: (a, b) -> a 
fst (x, y) = x 

{-@ reflect snd @-}
snd :: (a, b) -> b 
snd (x, y) = y 

{-@ reflect select @-}
{-@ select :: _ -> l:_ -> (a, {v:_|len v = len l }) @-}
select :: (Ord a) => a -> [a] -> (a, [a])
select x []    = (x, [])
select x (h:t) 
  | x <= h     = let xt = select x t in (fst xt, h : snd xt)
                 -- let (j, l') = select x t in (j, h:l')  
  | otherwise  = let ht = select h t in (fst ht, x : snd ht)
                 -- let (j, l') = select h t in (j, x:l') 

{-@ reflect selsort @-}
selsort :: (Ord a) => [a] -> [a]
selsort []     = [] 
selsort (x:xs) = y : selsort ys 
  where 
    (y, ys)    = select x xs 

-- | Proof of Correctness -----------------------------------------------------

{-@ reflect consElems @-}
consElems :: (Ord a) => a -> [a] -> S.Set a
consElems x ys = S.union (S.singleton x) (lElems ys) 

{-@ reflect pElems @-}
pElems :: (Ord a) => (a, [a]) -> S.Set a
pElems (x, ys) = consElems x ys

{-@ lem_select_perm :: x:_ -> xs:_ -> {consElems x xs = pElems (select x xs)} @-}
lem_select_perm :: (Ord a) => a -> [a] -> Proof 
lem_select_perm _ []    = () 
lem_select_perm x (h:t) 
  | x <= h              = lem_select_perm x t
  | otherwise           = lem_select_perm h t 

{-@ thm_selsort_perm :: xs:_ -> {perm xs (selsort xs)} @-}
thm_selsort_perm :: (Ord a) => [a] -> Proof
thm_selsort_perm []     = ()
thm_selsort_perm (x:xs) = lem_select_perm x xs &&& thm_selsort_perm ys 
  where 
    (y,ys)              = select x xs

-- | Proof of Sortedness ----

{-@ reflect leq @-}
leq :: (Ord a) => a -> a -> Bool 
leq x y = x <= y 

{-@ type Leqs X Ys = All Ys (leq X) @-}

{-@ lem_leq_sort :: x:_ -> ys:{sorted ys} -> Leqs x ys -> { sorted (cons x ys) } @-}
lem_leq_sort :: (Ord a) => a -> [a] -> (a -> Proof) -> Proof 
lem_leq_sort _ []     _  = () 
lem_leq_sort x (y:ys) pf = pf y 

{-@ lem_select_1 :: x:_ -> l:_ -> { fst (select x l) <= x } @-}
lem_select_1 :: (Ord a) => a -> [a] -> Proof 
lem_select_1 _ []    = () 
lem_select_1 x (h:t) 
  | x <= h           = fst (select x (h:t)) === fst (select x t) ? lem_select_1 x t =<= x *** QED 
  | otherwise        = fst (select x (h:t)) === fst (select h t) ? lem_select_1 h t =<= x *** QED


{-@ lem_select_r :: x:_ -> l:_ -> Leqs (fst (select x l)) (snd (select x l)) @-}
lem_select_r :: (Ord a) => a -> [a] -> a -> Proof
lem_select_r _ []    = const ()
lem_select_r x (h:t) 
  | x <= h           = let xt = select x t     ? lem_select_perm x t
                           xl = select x (h:t) ? lem_select_perm x (h:t)
                           pf = lem_select_r x t 
                       in \z -> if z == h || z == x 
                                  then fst xl === fst xt ? lem_select_1 x t =<= x =<= z *** QED 
                                  else fst xl === fst xt ? pf z                   =<= z *** QED 
                       -- lem_select_1 x t :: j <= x 

  | otherwise        = undefined

-- foo :: x:_ -> h:_ -> t:_ -> { S.subset (pElems (snd (select (x (h:t))))) (S.add x (S.add h (S.t 

   -- x in pElems (snd (select x l))     ==> x in pElems (snd (select x t))
   -- z in pElems (snd (select x (h:t))) ==> z == h || z in pElems (snd (select x t))

   
   --   GIVEN pf :: z in (snd xt) -> (fst xt) <= z  
   --   GOAL  z in 
   --   z in (snd xl) ===> pf z :: (fst xt) 


{-@ lem_select_min :: x:_ -> l:_ -> p:{p = select x l} -> Leqs (fst p) (snd p) @-}
lem_select_min :: (Ord a) => a -> [a] -> (a, [a]) -> a -> Proof
lem_select_min _ []    _ = const () 
lem_select_min x (h:t) p 
  | x <= h               = -- let (j, l') = select x t  
                           -- in  (j, h:l')
                           let xt = select x t 
                               pf = lem_select_min x t xt -- :: Leqs j l' 
                           in 
                              undefined  
  | otherwise            = undefined

{- select x (h:t) 
  | x <= h     = let (j, l') = select x t  
                 in (j, h:l')  
  | otherwise  = let (j, l') = select h t 
                 in (j, x:l') 
 -}

{-@ thm_selsort_sort :: xs:_ -> {sorted (selsort xs)} @-}
thm_selsort_sort :: (Ord a) => [a] -> Proof 
thm_selsort_sort []     = () 
thm_selsort_sort (x:xs) = lem_leq_sort y ys' leq_y_ys'
  where 
    (y, ys)             = select x xs 
    leq_y_ys            = lem_select_min x xs (select x xs) 
    ys'                 = selsort ys ? thm_selsort_perm ys ? thm_selsort_sort ys
    leq_y_ys'           = thm_perm_prop (leq y) ys ys' leq_y_ys


{-# ANN module "HLint: ignore Use camelCase" #-}