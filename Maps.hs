{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

module Maps where

import Language.Haskell.Liquid.NewProofCombinators

data Id = Id Int
          deriving (Eq)

data TotalMap a = TM
  { tmDef  :: a
  , tmVals :: [(Id, a)]
  }

{-@ reflect t_empty @-}
t_empty :: a -> TotalMap a
t_empty v = TM v []

{-@ reflect t_update @-}
t_update :: TotalMap a -> Id -> a -> TotalMap a
t_update (TM d kvs) k v = TM d ((k, v) : kvs)

{-@ reflect t_read @-}
t_read :: TotalMap a -> Id -> a
t_read (TM d kvs) key = lookupDefault d key kvs

{-@ reflect lookupDefault @-}
lookupDefault :: (Eq k) => v -> k -> [(k, v)] -> v
lookupDefault d key ((k,v) : kvs)
  | k == key           = v
  | otherwise          = lookupDefault d key kvs
lookupDefault d _   [] = d

{-@ reflect exMap @-}
exMap :: TotalMap Int
exMap = t_update (t_update (TM 99 []) (Id 10) 1) (Id 20) 2

{-@ propOK :: () -> TT @-}
propOK () = t_read exMap (Id 50) == 99
         && t_read exMap (Id 10) == 1
         && t_read exMap (Id 20) == 2

-- RJ:FAIL
{- propBAD :: () -> TT @-}
propBAD () = t_read m     (Id 50) == 99       -- RJ:WHY DOES THIS FAIL?!
          -- && t_read exMap (Id 10) == 1
          -- && t_read exMap (Id 20) == 2
  where
    m = exMap

{-@ t_apply_empty :: x:Id -> v:a -> { t_read (t_empty v) x == v } @-}
t_apply_empty :: Id -> a -> ()
t_apply_empty x v = ()

{-@ t_update_eq :: m:TotalMap a -> v:a -> x:Id -> { t_read (t_update m x v) x == v } @-}
t_update_eq :: TotalMap a -> a -> Id -> ()
t_update_eq m v x = ()

{-@ t_update_neq :: m:TotalMap a -> v:a -> x1:Id -> x2:{Id | x1 /= x2} ->
                      { t_read (t_update m x1 v) x2 == t_read m x2 }
  @-}
t_update_neq :: TotalMap a -> a -> Id -> Id -> ()
t_update_neq m v x1 x2 = ()

{-@ type EqMap a M1 M2 = x:Id -> { t_read M1 x == t_read M2 x } @-}

{-@ t_update_shadow :: m:TotalMap a -> v1:a -> v2:a -> x:Id ->
                         EqMap a (t_update (t_update m x v1) x v2) (t_update m x v2)
  @-}
t_update_shadow :: TotalMap a -> a -> a -> Id -> Id -> ()
t_update_shadow m v1 v2 x y
  | x == y    = ()
  | otherwise = ()

{-@ t_update_same :: m:TotalMap a -> x:Id -> EqMap a (t_update m x (t_read m x)) m @-}
t_update_same :: TotalMap a -> Id -> Id -> ()
t_update_same m x y
  | x == y    = ()
  | otherwise = ()

{-@ t_update_permute
      :: m:TotalMap a -> x1:Id -> x2:{Id | x1 /= x2} -> v1:a -> v2:a ->
          EqMap a (t_update (t_update m x1 v1) x2 v2) (t_update (t_update m x2 v2) x1 v1)
  @-}
t_update_permute :: TotalMap a -> Id -> Id -> a -> a -> Id -> ()
t_update_permute m x1 x2 v1 v2 y
  | y == x1   = ()
  | y == x2   = ()
  | otherwise = ()
