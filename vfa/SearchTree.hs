{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple"        @-} 
{-@ LIQUID "--diff"       @-} 

module SearchTree where

import           ProofCombinators
import qualified TotalMaps as T

import Prelude hiding (abs)

------------------------------------------------------------------------------
-- | Binary Search Trees -------------------------------------------------------
------------------------------------------------------------------------------

data Map k v
  = Leaf
  | Node k v (Map k v) (Map k v)

-- TODO: struct-termination issue 
-- https://github.com/ucsd-progsys/liquidhaskell/issues/1396

{-@ measure size @-}
{-@ size :: Map k v -> Nat @-}
size :: Map k v -> Int
size Leaf           = 0
size (Node k v l r) = 1 + size l + size r    


------------------------------------------------------------------------------
-- | Representation Invariant ------------------------------------------------
------------------------------------------------------------------------------

-- | Representation encoded as within datatype -------------------------------

{-@ data Map [size] k v = 
        Leaf
      | Node { mKey   :: k
             , mVal   :: v 
             , mLeft  :: Map {k:_ | k < mKey} v
             , mRight :: Map {k:_ | mKey < k} v
             } 
  @-} 

{-@ searchTree :: _  -> TT @-} 
searchTree :: (Ord k) => Map k v -> Bool 
searchTree Leaf           = True  
searchTree (Node k v l r) =  all_keys   l (< k) 
                          && all_keys   r (k <) 
                          && searchTree l 
                          && searchTree r

{-@ all_keys :: forall <p :: k -> Bool>. Map (k<p>) v -> (k<p> -> TT) -> TT @-} 
all_keys :: Map k v -> (k -> Bool) -> Bool
all_keys Leaf _           = True 
all_keys (Node k _ l r) p = p k && all_keys l p && all_keys r p

-- | For every `m :: Map k v` the function `searchTree m` returns `True`
lem_searchtree :: (Ord k) => Map k v -> Bool
lem_searchtree m = searchTree m == True 

------------------------------------------------------------------------------
-- | Map Operations ------------------------------------------------------------
------------------------------------------------------------------------------

{-@ reflect emp @-}
emp :: Map k v
emp = Leaf 

{-@ reflect get @-}
get :: (Ord k) => Map k v -> k -> Maybe v
get (Node k v l r) key
  | key == k  = Just v
  | key <  k  = get l key
  | otherwise = get r key
get Leaf _    = Nothing 


{-@ reflect set @-}
set :: (Ord k) => Map k v -> k -> v -> Map k v
set (Node k v l r) key val 
  | key == k     = Node key val l r
  | key <  k     = Node k v (set l key val) r
  | otherwise    = Node k v l (set r key val)
set Leaf key val = Node key val Leaf Leaf

------------------------------------------------------------------------------
-- | Map Laws ------------------------------------------------------------------
------------------------------------------------------------------------------

{-@ lem_get_eq :: (Ord k) => m:_ -> key:_ -> val:_ -> 
      { get (set m key val) key = Just val }
  @-}
lem_get_eq :: (Ord k) => Map k v -> k -> v -> Proof
lem_get_eq (Node k v l r) key val
  | key == k        = () 
  | key <  k        = lem_get_eq l key val
  | otherwise       = lem_get_eq r key val
lem_get_eq Leaf _ _ = () 

{-@ lem_get_neq :: (Ord k) => m:_ -> k1:_ -> k2:{k2 /= k1} -> v:_ -> 
      { get (set m k2 v) k1 = get m k1 }
  @-}
lem_get_neq :: (Ord k) => Map k v -> k -> k -> v -> Proof
lem_get_neq Leaf k1 k2 _ 
  | k1 < k2             = () 
  | otherwise           = () 
lem_get_neq (Node k v l r) k1 k2 v2 
  | k1 <  k, k  < k2    = () 
  | k  == k2            = () 
  | k1 == k, k  < k2    = () 
  | k2 <  k, k == k1    = () 
  | k2 <  k, k  < k1    = () 
  | k1 <  k, k2 < k     = lem_get_neq l k1 k2 v2
  | k  < k1, k  < k2    = lem_get_neq r k1 k2 v2

------------------------------------------------------------------------------
-- | An example Map -----------------------------------------------------------
------------------------------------------------------------------------------

{-@ reflect exMap @-}
exMap :: () -> Map Int String 
exMap _ = set (set (set emp 10 "cat") 20 "dog") 30 "zebra"

{-@ propOK :: () -> TT @-}
propOK () = get ex 10 == Just "cat" 
         && get ex 20 == Just "dog"
         && get ex 30 == Just "zebra"
         && get ex 0  == Nothing
  where 
    ex    = exMap ()


------------------------------------------------------------------------------
-- | Abstraction Function -----------------------------------------------------  
------------------------------------------------------------------------------

type TMap k v = T.TotalMap k (Maybe v)

{-@ reflect abs @-}
abs :: (Ord k) => Map k v -> TMap k v
abs (Node k v l r) key = combine k v (abs l) (abs r) key 
abs Leaf           key = Nothing

{-@ reflect combine @-}
combine :: (Ord k) => k -> v -> TMap k v -> TMap k v -> TMap k v 
combine key val lm rm k
  | k < key   = lm k 
  | key < k   = rm k
  | otherwise = Just val

------------------------------------------------------------------------------
-- | When are two functions extensionally equal ------------------------------
------------------------------------------------------------------------------

{-@ type ExtEq F G = kExtEq:_ -> { F kExtEq = G kExtEq } @-}

------------------------------------------------------------------------------
-- | `abs` is a legitimate ---------------------------------------------------
------------------------------------------------------------------------------

-- | The empty Map is equal to the empty TotalMap

{-@ lem_abs_emp :: ExtEq (abs emp) (T.def Nothing) @-}
lem_abs_emp :: k -> Proof 
lem_abs_emp _ = ()

-- | A 'get' returns the same value as the 'abs' total map 

{-@ lem_abs_get :: m:_ -> ExtEq (abs m) (get m)  @-} 
lem_abs_get :: (Ord k) => Map k v -> k -> Proof 
lem_abs_get (Node k v l r) key 
  | key < k          = lem_abs_get l key 
  | k < key          = lem_abs_get r key 
  | otherwise        = () 
lem_abs_get Leaf key = ()

-- | A 'set' on a  Map' yields a 'set' on the abstraction

{-@ lem_abs_set :: m:_ -> k:_ -> v:_ -> 
      ExtEq (T.set (abs m) k (Just v)) (abs (set m k v)) 
  @-} 
lem_abs_set :: (Ord k) => Map k v -> k -> v -> k -> Proof 
lem_abs_set m k v key 
  | key == k  = () --  T.set (abs m) k (Just v) key
              ? T.lem_get_set_eq (abs m) k (Just v)  
              -- === Just v 
              ? lem_get_eq m k v
              -- === get m' key
              ? lem_abs_get m' key 
              -- === abs m' key 

  | otherwise = () -- T.set (abs m) k (Just v) key 
              ? T.lem_get_set_neq (abs m) k (Just v)
              -- === abs m key
              ? lem_abs_get m key
              -- === get m key
              ? lem_get_neq m key k v
              -- === get m' key
              ? lem_abs_get (set m k v) key
              -- === abs m' key 

  where m'    = set m k v


