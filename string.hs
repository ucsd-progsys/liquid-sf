{-@ LIQUID "--exact-data-con"  @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--no-termination"  @-}
{- LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--higherorder"                         @-}

module String where

import Language.Haskell.Liquid.Prelude

type Key = Int

data Dict v = Emp | Key {dKey :: Key, dVal :: v, dRest :: Dict v}
{-@ data Dict v = Emp | Key {dKey :: Key, dVal :: v, dRest :: Dict v} @-}

{-@ reflect hasKey @-}
hasKey :: Key -> Dict a -> Bool
hasKey k Emp         = False
hasKey k (Key x v d) = k == x || hasKey k d

{-@ lazy die @-}
die :: a -> b
die a = die a

{-@ get :: k:String -> {d:Dict Int | hasKey k d} -> Int @-}
get :: String -> Dict Int -> Int
get k d1@(Key x v d)
  | k == x    = v
  | otherwise = liquidAssert (hasKey k d1) (get k d)
get k Emp     = 0

{-@ reflect tCatDog @-}
tCatDog :: Dict a -> Bool
tCatDog d = hasKey ("cat" :: String) d && hasKey ("dog" :: String) d

{-@ d1 :: {d:Dict Int | tCatDog d} @-}
d1 :: Dict Int
d1 = Key "cat" 10 (Key "dog" 20 Emp)
