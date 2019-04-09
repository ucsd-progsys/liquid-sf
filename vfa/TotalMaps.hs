{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module TotalMaps where

import ProofCombinators

-- | A total map is a function from `k` to `v` 

type TotalMap k v = k -> v

-- | A map that returns a `def`ault value
{-@ reflect def @-}
def :: v -> TotalMap k v
def v _ = v  

-- | Return the value of a given key `k`
{-@ reflect get @-}
get :: TotalMap k v -> k -> v  
get m k = m k

-- | Update the value of `k` with a value `v`
{-@ reflect set @-}
set :: (Eq k) => TotalMap k v -> k -> v -> TotalMap k v
set m k v key 
  | key == k  = v 
  | otherwise = get m key

-- | An example map
{-@ reflect exMap @-}
exMap :: TotalMap Int String
exMap k = (set (set (set (def "nothing") 10 "cat") 20 "dog") 30 "zebra") k

{-@ test :: () -> TT @-}
test () =  get exMap 10 == "cat" 
        && get exMap 20 == "dog"
        && get exMap 30 == "zebra"
        && get exMap 0  == "nothing"

-- | A default map has the same value for all keys.
{-@ lem_get_def :: key:_ -> v:_ -> { get (def v) key == v } @-}
lem_get_def :: k -> v -> Proof 
lem_get_def _ _ = ()

-- | Reading an updated key yields the newly updated value 
{-@ lem_get_set_eq :: m:_ -> key:_ -> val:_ -> 
      { get (set m key val) key == val } 
  @-}
lem_get_set_eq :: TotalMap k v -> k -> v -> Proof 
lem_get_set_eq _ _ _ = ()

-- | Reading an un-updated key yields the original value 
{-@ lem_get_set_neq :: m:_ -> k1:_ -> v:_ -> k2:{k2 /= k1} -> 
      { get (set m k1 v) k2 == get m k2 } 
  @-}
lem_get_set_neq :: TotalMap k v -> k -> v -> k -> Proof 
lem_get_set_neq _ _ _ _ = ()


-- | (Extensional) Equality on maps ---------------------------------------------- 

{-@ type EqMap M1 M2 = keq:_ -> { get M1 keq == get M2 keq } @-}

-- | Shadowing the same key with a new write is equivalent to skipping the old write.

{-@ lem_set_shadow :: m:_ -> k:_ -> v1:_ -> v2:_ -> 
      EqMap (set (set m k v1) k v2) (set m k v2) 
  @-}
lem_set_shadow :: (Eq k) => TotalMap k v -> k -> v -> v -> k -> Proof 
lem_set_shadow m k v1 v2 key 
  | key == k  = ()
  | otherwise = ()

-- | Updating a key with the same value is equivalent to the original map 

{-@ lem_set_same :: m:_ -> k:_ -> EqMap m (set m k (get m k)) 
  @-}
lem_set_same :: (Eq k) => TotalMap k v -> k -> k -> Proof
lem_set_same m k key 
  | key == k  = ()
  | otherwise = ()

-- | We can commute / permute updates to different keys 

{-@ lem_set_perm :: m:_ -> k1:_ -> k2:{k2 /= k1} -> v1:_ -> v2:_ ->
          EqMap (set (set m k1 v1) k2 v2) (set (set m k2 v2) k1 v1)
  @-}
lem_set_perm :: (Eq k) => TotalMap k v -> k -> k -> v -> v -> k -> Proof
lem_set_perm m k1 k2 v1 v2 key
  | key == k1 = ()
  | key == k2 = ()
  | otherwise = ()
