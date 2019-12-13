{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}
{-@ LIQUID "--exactdc"                             @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}

module BST where
import qualified Data.Set as S
import Language.Haskell.Liquid.ProofCombinators 
import Prelude hiding (lookup, Maybe(..))


data Maybe a = Just a | Nothing 


{-@ measure isJust @-}
isJust :: Maybe a -> Bool  
isJust (Just _) = True 
isJust Nothing  = False 

{-@ measure fromJust @-}
{-@ fromJust :: {v:Maybe a | isJust v } -> a @-}
fromJust :: Maybe a -> a 
fromJust (Just x) = x 


data BST k v = Empty | Bind k v (BST k v) (BST k v)

 
{-@
data BST [blen] k v = Empty
  | Bind { bKey   :: k
         , bValue :: v
         , bLeft  :: BST k v
         , bRight :: BST k v }
@-}


{-@ measure blen @-}
blen :: (BST k v) -> Int
{-@ blen :: (BST k v) -> Nat @-}
blen(Empty)        = 0
blen(Bind k v l r) = 1 + (blen l) + (blen r)


{-@ reflect insert @-}
insert :: (Eq k, Ord k) => k -> v -> BST k v -> BST k v
insert k v Empty  = Bind k v Empty Empty
insert k v (Bind k' v' l r)
  | k == k'       = Bind k v l r
  | k < k'        = Bind k' v' (insert k v l) r
  | otherwise     = Bind k' v' l (insert k v r)


{-@ reflect lookup @-}
lookup :: (Eq k, Ord k) => k -> BST k v -> Maybe v
lookup k Empty  = Nothing
lookup k (Bind k' v l r)
  | k == k'       = Just v
  | k < k'        = lookup k l
  | otherwise     = lookup k r


{-@ elements1 :: (Eq k, Ord k) => BST k v -> [(k,v)] -> [(k,v)]@-}
elements1:: (Eq k, Ord k) => BST k v -> [(k,v)] -> [(k,v)]
elements1  Empty list                = list
elements1  (Bind k v l r) list = elements1 l ((k,v) : (elements1 r list))


{-@ elements :: (Eq k, Ord k) => BST k v -> [(k,v)] @-}
elements:: (Eq k, Ord k) => BST k v -> [(k,v)] 
elements bst = elements1 bst []


lookup_el :: (Eq k, Ord k) => k ->  [(k, v)] -> (Maybe v)
lookup_el k [] = Nothing
lookup_el k ( (k1,v1):ks ) = if(k == k1) then (Just v1) else lookup_el k ks


{-@ reflect searchTree @-}
{-@ searchTree :: Nat ->  t:BST Nat v -> Nat -> Bool / [blen t]@-}
searchTree :: Int ->  BST Int v -> Int -> Bool
searchTree lo (Empty)        hi = (lo<=hi)
searchTree lo (Bind k v l r) hi = (searchTree lo l k) && (searchTree (k+1) r hi)


{-@ lemma_SearchTree_le :: lo: Nat -> hi: Nat -> t:{ BST Nat v | searchTree lo t hi} -> {lo <= hi} / [blen t] @-}
lemma_SearchTree_le :: Int -> Int -> BST Int v -> Proof
lemma_SearchTree_le lo hi Empty        = trivial
lemma_SearchTree_le lo hi (Bind k v l r) = [lemma_SearchTree_le lo k l, lemma_SearchTree_le (k+1) hi r] *** QED


{-@ empty_tree_SearchTree :: lo: Nat -> hi: {Nat | lo <= hi } -> {searchTree lo Empty hi} @-}
empty_tree_SearchTree :: Int -> Int -> Proof
empty_tree_SearchTree lo hi = trivial


{-@ theorem_insert_SearchTree :: k:Nat -> vk: v -> lo:{Int | lo<=k } -> hi:{Int | k<hi } -> t:{BST Nat v | searchTree lo t hi } 
    -> {searchTree lo (insert k vk t) hi} / [blen t]
@-}
theorem_insert_SearchTree :: Int -> v -> Int -> Int -> BST Int v -> Proof
theorem_insert_SearchTree k v lo hi Empty = trivial
theorem_insert_SearchTree k v lo hi (Bind k1 v1 l r) 
          | k==k1 = trivial
          | k<k1 = theorem_insert_SearchTree k v lo k1 l
          | k>k1 = theorem_insert_SearchTree k v (k1+1) hi r


{-@ t_apply_empty :: (Eq k, Ord k, Eq v) => x :k -> v1 :v -> { lookup x (Bind x v1 Empty Empty) = (Just v1) } @-}
t_apply_empty :: (Eq k, Ord k, Eq v) => k -> v -> Proof
t_apply_empty x v1 = (lookup x (Bind x v1 Empty Empty) ) *** QED


{-@ t_update_eq :: (Eq k, Ord k, Eq v) => t: (BST k v) -> x:k -> v1 :v -> { lookup x (insert x v1 t) = (Just v1) } @-}
t_update_eq :: (Eq k, Ord k, Eq v) => (BST k v) -> k -> v -> Proof
t_update_eq Empty x v1  =   lookup x (insert x v1 Empty)
                        ==. lookup x (Bind x v1 Empty Empty) 
                        ==. (Just v1) 
                        *** QED

t_update_eq (Bind k v l r) x v1 
      | k == x =   lookup x (insert x v1 (Bind k v l r))
               ==. lookup x (Bind x v1 l r)
               ==. Just v1
               *** QED

      | k <  x =   lookup x (insert x v1 (Bind k v l r))
               ==. lookup x ( Bind k v l (insert x v1 r))
               ==. lookup x (insert x v1 r)
               ==. (Just v1) ? t_update_eq r x v1 
               *** QED

      | k > x =   lookup x (insert x v1 (Bind k v l r))
              ==. lookup x ( Bind k v (insert x v1 l) r)
              ==. lookup x (insert x v1 l)
              ==. (Just v1) ? t_update_eq l x v1 
              *** QED


{-@ t_update_neq :: (Eq k, Ord k, Eq v) => k1:k -> k2:{k | k1 /= k2} -> v2:v -> t: (BST k v)  ->
                      { lookup k1 (insert k2 v2 t) == lookup k1 t }
@-}
t_update_neq :: (Eq k, Ord k, Eq v) => k -> k -> v -> (BST k v) -> Proof
t_update_neq k1 k2 v2 Empty
  | k1 < k2             =   lookup k1 (insert k2 v2 Empty)
                        ==. lookup k1 (Bind k2 v2 Empty Empty)
                        ==. lookup k1 Empty
                        *** QED

  | otherwise           =   lookup k1 (insert k2 v2 Empty)
                        ==. lookup k1 (Bind k2 v2 Empty Empty)
                        ==. lookup k1 Empty
                        *** QED

t_update_neq k1 k2 v2 (Bind k v l r)
  | k1 <  k, k <  k2    =   lookup k1 (insert k2 v2 (Bind k v l r))
                        ==. lookup k1 (Bind k v l (insert k2 v2 r))
                        ==. lookup k1 (Bind k v l r)
                        *** QED

  | k == k2             =   lookup k1 (insert k2 v2 (Bind k v l r))
                        ==. lookup k1 (Bind k v2 l r)
                        ==. lookup k1 (Bind k v l r)
                        *** QED

  | k1 == k, k <  k2    =   lookup k1 (insert k2 v2 (Bind k v l r))
                        ==. lookup k1 (Bind k v l (insert k2 v2 r))
                        ==. lookup k1 (Bind k v l r)
                        *** QED

  | k2 <  k, k == k1    =   lookup k1 (insert k2 v2 (Bind k v l r))
                        ==. lookup k1 (Bind k v (insert k2 v2 l) r)
                        ==. lookup k1 (Bind k v l r)
                        *** QED

  | k2 <  k, k <  k1    =   lookup k1 (insert k2 v2 (Bind k v l r))
                        ==. lookup k1 (Bind k v (insert k2 v2 l) r)
                        ==. lookup k1 r
                        ==. lookup k1 (Bind k v l r)
                        *** QED

  | k1 < k, k2 < k      =   lookup k1 (insert k2 v2 (Bind k v l r))
                        ==. lookup k1 (Bind k v (insert k2 v2 l) r)
                        ==. lookup k1 (insert k2 v2 l)   ? t_update_neq k1 k2 v2 l
                        ==. lookup k1 l
                        ==. lookup k1 (Bind k v l r)
                        *** QED

  | k < k1, k < k2      =   lookup k1 (insert k2 v2 (Bind k v l r))
                        ==. lookup k1 (Bind k v l (insert k2 v2 r))
                        ==. lookup k1 (insert k2 v2 r)   ? t_update_neq k1 k2 v2 r
                        ==. lookup k1 r
                        ==. lookup k1 (Bind k v l r)
                        *** QED


{-@ thm_same_tree ::  (Eq k, Ord k, Eq v) => t:(BST k v) -> v1:v -> v2:v -> x:k 
    -> { (insert x v2 (insert x v1 t)) = (insert x v2 t) } @-}
thm_same_tree ::  (Eq k, Ord k, Eq v) => (BST k v) -> v -> v -> k -> Proof    

thm_same_tree Empty v1 v2 x =   (insert x v2 (insert x v1 Empty)) 
                            ==. (insert x v2  (Bind x v1 Empty Empty))
                            ==. (Bind x v2 Empty Empty)
                            ==. (insert x v2 Empty)
                            *** QED

thm_same_tree (Bind x1 v l r) v1 v2 x 

      | x == x1 =  (insert x v2 (insert x v1 (Bind x v l r))) 
                ==. (insert x v2  (Bind x v1 l r))
                ==. (Bind x v2 l r)
                ==. (insert x v2 (Bind x1 v l r))
                *** QED 

      | x < x1  =   (insert x v2 (insert x v1 (Bind x1 v l r))) 
                ==. (insert x v2  (Bind x1 v (insert x v1 l) r))
                ==. (Bind x1 v (insert x v2 (insert x v1 l)) r)
                ==. (Bind x1 v (insert x v2 l) r)     ? thm_same_tree l v1 v2 x
                ==. (insert x v2 (Bind x1 v l r))
                *** QED 
                 
      | x > x1  =   (insert x v2 (insert x v1 (Bind x1 v l r))) 
                ==. (insert x v2  (Bind x1 v l (insert x v1 r)))
                ==. (Bind x1 v l (insert x v2 (insert x v1 r)))
                ==. (Bind x1 v l (insert x v2 r))     ? thm_same_tree r v1 v2 x
                ==. (insert x v2 (Bind x1 v l r))
                *** QED 


{-@ type EqTree k v T1 T2 = x:k -> { lookup x T1 == lookup x T2 } @-}


{-@ t_update_shadow :: (Eq k, Ord k, Eq v) => t:(BST k v) -> v1:v -> v2:v -> x:k ->
                         EqTree k v (insert x v2 (insert x v1 t)) (insert x v2 t)
@-}

t_update_shadow :: (Eq k, Ord k, Eq v) => (BST k v) -> v -> v -> k -> k -> Proof
t_update_shadow t v1 v2 x y = (thm_same_tree t v1 v2 x) *** QED


{-@ t_update_same :: (Eq k, Ord k, Eq v) => t:(BST k v) -> x: {k | isJust (lookup x t) } 
         -> EqTree k v (insert x (fromJust (lookup x t)) t)  t @-}
t_update_same :: (Eq k, Ord k, Eq v) => (BST k v) ->  k -> k -> Proof
t_update_same t x y = (t_update_same_aux t x)*** QED


{-@ t_update_same_aux 
  :: (Eq k, Ord k, Eq v) 
  => t:BST k v 
  -> x: {k | isJust (lookup x t) }  
  ->  {(insert x (fromJust (lookup x t)) t) == t} @-}
t_update_same_aux 
  :: (Eq k, Ord k, Eq v)
  => BST k v -> k -> Proof 
t_update_same_aux (Bind k v l r) x 
  | x == k
  =   insert x (fromJust (lookup x (Bind x v l r))) (Bind x v l r)
  ==. insert x (fromJust (Just v)) (Bind x v l r)
  ==. insert x v (Bind x v l r)
  ==. Bind x v l r
  *** QED 
  | x < k
  =   insert x (fromJust (lookup x (Bind k v l r))) (Bind k v l r)
  ==. insert x (fromJust (lookup x l)) (Bind k v l r)
  ==. Bind k v (insert x (fromJust (lookup x l)) l) r
       ? t_update_same_aux l x
  ==. Bind k v l r  
  *** QED 
  | x > k  
  =   insert x (fromJust (lookup x (Bind k v l r))) (Bind k v l r)
  ==. insert x (fromJust (lookup x r)) (Bind k v l r)
  ==. Bind k v l (insert x (fromJust (lookup x r)) r)
       ? t_update_same_aux r x
  ==. Bind k v l r  
  *** QED 
t_update_same_aux Empty x 
  =   isJust (lookup x Empty) 
  ==. isJust Nothing
  *** QED 


{-@ t_update_permute :: (Eq k, Ord k, Eq v) => t: (BST k v) -> x1:k -> x2:{k | x1 /= x2} -> y:k -> v1:v -> v2:v ->
          { lookup y (insert x2 v2 (insert x1 v1 t)) == lookup y (insert x1 v1 (insert x2 v2 t)) }
@-}
t_update_permute :: (Eq k, Ord k, Eq v) => (BST k v) -> k -> k -> k -> v -> v -> Proof
t_update_permute t x1 x2 y v1 v2  | x1 == x2 = trivial
t_update_permute t x1 x2 y v1 v2  
        |  y == x2  = [ t_update_eq (insert x1 v1 t) x2 v2 , t_update_neq y x1 v1 (insert y v2 t ) , t_update_eq t y v2 ] *** QED
        |  y == x1  = [ t_update_eq (insert x2 v2 t) x1 v1 , t_update_neq y x2 v2 (insert y v1 t ) , t_update_eq t y v1 ] *** QED
        | otherwise = [ t_update_neq y x2 v2 (insert x1 v1 t) , t_update_neq y x1 v1 (insert x2 v2 t),
                        t_update_neq y x1 v1 t , t_update_neq y x2 v2 t ] *** QED

