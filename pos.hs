{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}


module Pos where 

{-@ reflect pos @-}
pos :: Int -> Int 
pos n = if n <= 0 then 0 else 1 + pos (n-1)

{-@ zing :: n:{Int | n > 100} -> {pos n = 9 + pos (n-9)} @-}
zing :: Int -> ()
zing _ = () 

{-@ pf :: f:(a -> a) ->x:{a | x == f(f(f(x))) && x = f(f(f(f(f(x))))) } -> {x = f(x)} @-}
pf :: (a -> a) -> a -> () 
pf _ _ = ()
