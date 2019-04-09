{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module TotalMaps where

import ProofCombinators

-- | A total map is a function from `k` to `v` 

type TotalMap k v = k -> v

-- | A map that returns a `def`ault value
{-@ reflect t_def @-}
t_def :: v -> TotalMap k v
t_def def _ = def 

-- | Return the value of a given key `k`
{-@ reflect t_get @-}
t_get :: TotalMap k v -> k -> v  
t_get m k = m k

-- | Update the value of `k` with a value `v`
{-@ reflect t_set @-}
t_set :: (Eq k) => TotalMap k v -> k -> v -> TotalMap k v
t_set m k v key 
  | key == k  = v 
  | otherwise = t_get m key

-- | An example map
{-@ reflect exMap @-}
exMap :: TotalMap String Int
exMap k = (t_set (t_set (t_set (t_def 0) "cat" 10) "dog" 20) "zebra" 30) k

{-@ propOK :: () -> TT @-}
propOK () = t_get exMap "cat"   == 10
         && t_get exMap "dog"   == 20
         && t_get exMap "zebra" == 30 
         && t_get exMap "horse" == 0

-- | A default map has the same value for all keys.
{-@ lem_get_def :: key:_ -> v:_ -> { t_get (t_def v) key == v } @-}
lem_get_def :: k -> v -> Proof 
lem_get_def _ _ = ()

-- | Reading an updated key yields the newly updated value 
{-@ lem_get_set_eq :: m:_ -> key:_ -> val:_ -> 
      { t_get (t_set m key val) key == val } 
  @-}
lem_get_set_eq :: TotalMap k v -> k -> v -> Proof 
lem_get_set_eq _ _ _ = ()

-- | Reading an un-updated key yields the original value 
{-@ lem_get_set_neq :: m:_ -> k1:_ -> v:_ -> k2:{k2 /= k1} -> 
      { t_get (t_set m k1 v) k2 == t_get m k2 } 
  @-}
lem_get_set_neq :: TotalMap k v -> k -> v -> k -> Proof 
lem_get_set_neq _ _ _ _ = ()


-- | (Extensional) Equality on maps ---------------------------------------------- 

{-@ type EqMap M1 M2 = keq:_ -> { t_get M1 keq == t_get M2 keq } @-}

-- | Shadowing the same key with a new write is equivalent to skipping the old write.

{-@ t_set_shadow :: m:_ -> k:_ -> v1:_ -> v2:_ -> 
      EqMap (t_set (t_set m k v1) k v2) (t_set m k v2) 
  @-}
t_set_shadow :: (Eq k) => TotalMap k v -> k -> v -> v -> k -> Proof 
t_set_shadow m k v1 v2 key 
  | key == k  = ()
  | otherwise = ()

-- | Updating a key with the same value is equivalent to the original map 

{-@ t_set_same :: m:_ -> k:_ -> EqMap m (t_set m k (t_get m k)) 
  @-}
t_set_same :: (Eq k) => TotalMap k v -> k -> k -> Proof
t_set_same m k key 
  | key == k  = ()
  | otherwise = ()

-- | We can commute / permute updates to different keys 

{-@ t_set_perm :: m:_ -> k1:_ -> k2:{k2 /= k1} -> v1:_ -> v2:_ ->
          EqMap (t_set (t_set m k1 v1) k2 v2) (t_set (t_set m k2 v2) k1 v1)
  @-}
t_set_perm :: (Eq k) => TotalMap k v -> k -> k -> v -> v -> k -> Proof
t_set_perm m k1 k2 v1 v2 key
  | key == k1 = ()
  | key == k2 = ()
  | otherwise = ()
