import Data.Monoid

{-@ bar :: [Nat] @-}
bar = xs1 <> xs2 

{-@ xs1, xs2 :: [Nat] @-}
xs1, xs2 :: [Int]
xs1 = [3, 4] 
xs2 = [1, 2]
