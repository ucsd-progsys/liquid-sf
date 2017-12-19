{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

module Poly where

import Prelude hiding ((++), map, rev, sum, foldMap)
import Language.Haskell.Liquid.NewProofCombinators

-- | List Definition -----------------------------------------------------------

{-@ data List [llen] @-}
data List a = Nil | Cons a (List a)
              deriving (Eq)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons h t) = 1 + llen t

-- | Append---------------------------------------------------------------------

{-@ reflect app @-}
app :: List a -> List a -> List a
app Nil         ys = ys
app (Cons x xs) ys = Cons x (app xs ys)

{-@ infix ++ @-}
{-@ reflect ++ @-}
xs ++ ys = app xs ys

{-@ reflect member @-}
member :: (Eq a) => a -> List a -> Bool
member x Nil         = False
member x (Cons y ys) = x == y || member x ys

-- | Reverse -------------------------------------------------------------------

{-@ reflect rev @-}
rev :: List a -> List a
rev Nil         = Nil
rev (Cons x xs) = (rev xs) ++ (Cons x Nil)

-- | Map -----------------------------------------------------------------------

{-@ reflect map @-}
map :: (a -> b) -> List a -> List b
map f Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

--------------------------------------------------------------------------------

{-@ thmAppAssoc :: xs:_ -> ys:_ -> zs:_
                -> {xs ++ (ys ++ zs) = (xs ++ ys) ++ zs}
  @-}
thmAppAssoc :: List a -> List a -> List a -> Proof
thmAppAssoc Nil ys zs         = trivial
thmAppAssoc (Cons x xs) ys zs = thmAppAssoc xs ys zs

{-@ thmAppNilR :: xs:List a -> {xs ++ Nil = xs} @-}
thmAppNilR :: List a -> Proof
thmAppNilR Nil         = trivial
thmAppNilR (Cons x xs) = thmAppNilR xs

{-@ thmRevAppDistr :: xs:List a -> ys:List a
                   -> {rev (xs ++ ys) = (rev ys) ++ (rev xs) }
  @-}
thmRevAppDistr :: List a -> List a -> Proof
thmRevAppDistr Nil ys
  =  [ -- rev (app Nil ys)
       -- ==. rev ys ?
       thmAppNilR (rev ys)
       -- ==. app (rev ys) Nil
     ] *** QED

thmRevAppDistr (Cons x xs) ys
  =  [ -- rev (app (Cons x xs) ys)
       -- ==. rev (Cons x (app xs ys))
       -- ==. app (rev (app xs ys)) (Cons x Nil) ?
       thmRevAppDistr xs ys
       -- ==. app (app (rev ys)  (rev xs)) (Cons x Nil) ?
     , thmAppAssoc (rev ys) (rev xs) (Cons x Nil)
       -- ==. app (rev ys) (app (rev xs) (Cons x Nil))
       -- ==. app (rev ys) (rev (Cons x xs))
     ] *** QED

{-@ thmMapAppDist :: f:_ -> xs:_ -> ys:_
                  -> {map f (xs ++ ys) = (map f xs) ++ (map f ys)}
  @-}
thmMapAppDist :: (a -> b) -> List a -> List a -> Proof
thmMapAppDist f Nil ys         = ()
thmMapAppDist f (Cons x xs) ys = thmMapAppDist f xs ys

{-@ thmMapRev :: f:_ -> xs:_ -> {map f (rev xs) = rev (map f xs)} @-}
thmMapRev :: (a -> b) -> List a -> Proof
thmMapRev f Nil
  = ()
thmMapRev f (Cons x xs)
  = [ --  map f (rev (Cons x xs))
      -- ==. map f (rev xs `app` (Cons x Nil))
      thmMapAppDist f (rev xs) (Cons x Nil)
      -- ==. map f (rev xs) `app` map f (Cons x Nil)
    , thmMapRev f xs
      -- ==. rev (map f xs) `app` (Cons (f x) Nil)
      -- ==. rev (Cons (f x) (map f xs))
      -- ==. rev (map f (Cons x xs))
    ] *** QED

-- | Fold ----------------------------------------------------------------------

{-@ reflect fold @-}
fold :: (a -> b -> b) -> b -> List a -> b
fold f b Nil = b
fold f b (Cons x xs) = f x (fold f b xs)

{-@ reflect plus @-}
plus :: Int -> Int -> Int
plus x y = x + y

{-@ reflect sum @-}
sum :: List Int -> Int
sum xs = fold plus 0 xs

{-@ test1 :: () -> { 6 = sum (Cons 1 (Cons 2 (Cons 3 Nil)))} @-}
test1 :: () -> ()
test1 _ = ()

{-@ reflect incr @-}
incr :: a -> Int -> Int
incr _ n = n + 1

{-@ reflect foldLen @-}
foldLen :: List a -> Int
foldLen xs = fold incr 0 xs

{-@ test2 :: () -> { 3 = foldLen (Cons 1 (Cons 2 (Cons 3 Nil)))} @-}
test2 :: () -> ()
test2 _ = ()

{-@ thmFoldLenCorrect :: xs:List a -> { llen xs = foldLen xs } @-}
thmFoldLenCorrect :: List a -> Proof
thmFoldLenCorrect Nil         = ()
thmFoldLenCorrect (Cons x xs) = thmFoldLenCorrect xs

{-@ reflect up @-}
up :: Int -> Int
up x = x + 1

{-@ thmMapIncr :: xs:List Int -> { tot (map up xs) == tot xs + myLen xs } @-}
thmMapIncr :: List Int -> Proof
thmMapIncr Nil         = ()
thmMapIncr (Cons x xs) = thmMapIncr xs
                       -- sum (map up (Cons x xs))
                       -- ==. sum (Cons (up x) (map up xs))
                       -- ==. fold plus 0 (Cons (up x) (map up xs))
                       -- ==. plus (up x) (fold plus 0 (map up xs))
                       -- ==. plus (up x) (sum (map up xs))
                           -- ? thmMapIncr xs
                       -- ==. plus (up x) (sum xs + llen xs)
                       -- ==. plus (x+1)  (sum xs + llen xs)
                       -- ==. (x + sum xs) + (1 + llen xs)
                       -- ==. sum (Cons x xs) + llen (Cons x xs)
                       -- *** QED

{-@ reflect myLen @-}
myLen :: List a -> Int
myLen Nil         = 0
myLen (Cons x xs) = 1 + myLen xs

{-@ reflect tot @-}
tot :: List Int -> Int
tot Nil         = 0
tot (Cons x xs) = x + tot xs

-- | FoldMap -------------------------------------------------------------------

{-@ reflect glob @-}
glob :: (a -> b) -> a -> List b -> List b
glob f x ys = Cons (f x) ys

{-@ reflect foldMap @-}
foldMap :: (a -> b) -> List a -> List b
foldMap f xs = fold (glob f) Nil xs

{-@ thmFoldMapCorrect :: f:_ -> xs:_ -> { map f xs = foldMap f xs } @-}
thmFoldMapCorrect :: (a -> b) -> List a -> Proof
thmFoldMapCorrect f Nil         = ()
thmFoldMapCorrect f (Cons x xs) = thmFoldMapCorrect f xs
