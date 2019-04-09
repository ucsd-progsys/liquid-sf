{-@ LIQUID "--reflection" @-} 
{- LIQUID "--ple"        @-} 
{- LIQUID "--diff"       @-} 

module SearchTree where

import ProofCombinators
import Prelude hiding (max)

-- | Options -------------------------------------------------------------------

data Option a = None | Some a

-- | Binary Search Trees -------------------------------------------------------

{-@ data Map [size] @-} 

data Map k v
  = Leaf
  | Node k v (Map k v) (Map k v)

{-@ measure size @-}
{-@ size :: Map k v -> Nat @-}
size :: Map k v -> Int
size Leaf           = 0
size (Node k v l r) = 1 + size l + size r    

-- | Map Operations ------------------------------------------------------------

{-@ reflect get @-}
get :: (Ord k) => k -> Map k v -> Option v
get key Leaf           = None
get key (Node k v l r)
  | key == k           = Some v
  | key <  k           = get key l
  | otherwise          = get key r


{-@ reflect set @-}
set :: (Ord k) => k -> v -> Map k v -> Map k v
set key val Leaf       = Node key val Leaf Leaf
set key val (Node k v l r)
  | key == k           = Node key val l r
  | key <  k           = Node k v (set key val l) r
  | otherwise          = Node k v l (set key val r)

-- | Map Laws ------------------------------------------------------------------

{-@ lem_get_eq :: (Ord k) => key:k -> val:v -> m:Map k v ->
      { get key (set key val m) = Some val }
  @-}
lem_get_eq :: (Ord k) => k -> v -> Map k v -> Proof
lem_get_eq key val Leaf =   get key (set key val Leaf)
                       === get key (Node key val Leaf Leaf)
                       === Some val
                       *** QED

lem_get_eq key val (Node k v l r)
  | key == k          =   get key (set key val (Node k v l r))
                      === get key (Node key val l r)
                      === Some val
                      *** QED

  | key <  k          =   get key (set key val (Node k v l r))
                      === get key (Node k v (set key val l) r)    -- THIS LINE IS NEEDED
                      === get key (set key val l)
                          ? lem_get_eq key val l
                      === Some val
                      *** QED

  | otherwise         =   get key (set key val (Node k v l r))
                      === get key (Node k v l (set key val r))    -- THIS LINE IS NEEDED
                      === get key (set key val r)
                          ? lem_get_eq key val r
                      === Some val
                      *** QED

{-@ thmGetNeq :: (Ord k) => k1:k -> k2:{k | k1 /= k2} -> v2:v -> m:Map k v ->
      { get k1 (set k2 v2 m) = get k1 m }
  @-}
thmGetNeq :: (Ord k) => k -> k -> v -> Map k v -> Proof
thmGetNeq k1 k2 v2 Leaf
  | k1 < k2             =   get k1 (set k2 v2 Leaf)
                        === get k1 (Node k2 v2 Leaf Leaf)
                        === get k1 Leaf
                        *** QED

  | otherwise           =   get k1 (set k2 v2 Leaf)
                        === get k1 (Node k2 v2 Leaf Leaf)
                        === get k1 Leaf
                        *** QED

thmGetNeq k1 k2 v2 (Node k v l r)
  | k1 <  k, k <  k2    =   get k1 (set k2 v2 (Node k v l r))
                        === get k1 (Node k v l (set k2 v2 r))
                        === get k1 (Node k v l r)
                        *** QED

  | k == k2             =   get k1 (set k2 v2 (Node k v l r))
                        === get k1 (Node k v2 l r)
                        === get k1 (Node k v l r)
                        *** QED

  | k1 == k, k <  k2    =   get k1 (set k2 v2 (Node k v l r))
                        === get k1 (Node k v l (set k2 v2 r))
                        === get k1 (Node k v l r)
                        *** QED

  | k2 <  k, k == k1    =   get k1 (set k2 v2 (Node k v l r))
                        === get k1 (Node k v (set k2 v2 l) r)
                        === get k1 (Node k v l r)
                        *** QED

  | k2 <  k, k <  k1    =   get k1 (set k2 v2 (Node k v l r))
                        === get k1 (Node k v (set k2 v2 l) r)
                        === get k1 r
                        === get k1 (Node k v l r)
                        *** QED

  | k1 < k, k2 < k      =   get k1 (set k2 v2 (Node k v l r))
                        === get k1 (Node k v (set k2 v2 l) r)
                        === get k1 (set k2 v2 l)
                            ? thmGetNeq k1 k2 v2 l
                        === get k1 l
                        === get k1 (Node k v l r)
                        *** QED

  | k < k1, k < k2      =   get k1 (set k2 v2 (Node k v l r))
                        === get k1 (Node k v l (set k2 v2 r))
                        === get k1 (set k2 v2 r)
                            ? thmGetNeq k1 k2 v2 r
                        === get k1 r
                        === get k1 (Node k v l r)
                        *** QED
