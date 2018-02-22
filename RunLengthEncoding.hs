{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple"             @-}

module RunLengthEncoding where

import Prelude hiding (id, head, replicate, span, (++))
import Language.Haskell.Liquid.NewProofCombinators

---------------------------------------------------------------------------
-- | Function composition
---------------------------------------------------------------------------
{-@ infix % @-}

{-@ reflect % @-}
(%) f g x = f (g x)
---------------------------------------------------------------------------

{-@ reflect inc @-}
inc :: Int -> Int
inc x = x + 1

{-@ reflect dec @-}
dec :: Int -> Int
dec x = x - 1

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ inc_ext :: { inc % dec == id } @-}
inc_ext :: ()
inc_ext = ext_axiom
            (inc % dec)
            id
            (\x -> (inc % dec) x == id x)

---------------------------------------------------------------------------
-- | Extensionality Axiom
---------------------------------------------------------------------------
{-@ assume ext_axiom :: (Protect a) => f:(a -> b) -> g:(a -> b) -> pf:(x:a -> {f x == g x}) -> {f == g} @-}
ext_axiom :: (Protect a) => (a -> b) -> (a -> b) -> (a -> pf) -> Proof
ext_axiom f g pf = undefined

class Protect a where
  protect :: a -> a
  protect x = x

instance Protect Int where
---------------------------------------------------------------------------


{-@ rle_thm :: () -> { decode % encode == id } @-}
rle_thm :: () -> ()
rle_thm _
  =   decode % encode
  === (concat % map decodeBlob) % encode
  ==? concat % (map decodeBlob % encode)                    ? assoc_comp concat (map decodeBlob) encode
  ==? concat % ((map decodeBlob % map encodeBlob) % group)  ? assoc_comp (map decodeBlob) (map encodeBlob) group
  ==? concat % ((map (decodeBlob % encodeBlob))   % group)  ? map_fusion decodeBlob encodeBlob
  ==? concat % ((map id)                          % group)  ? encBlob_decBlob_inv
  ==? concat % (id                                % group)  ? map_id
  ==? concat % group                                        ? comp_id_left
  ==? id                                                    ? concat_group_inv
  *** QED

{-
assoc_4
  =  (a % b) % (c % d)
  === a % (b % (c % d)) ? assoc_comp a b (c % d)
  === a % ((b % c) % d) ? assoc_comp b c d


map_fusion :: f:_ -> g:_ -> map f % map g == map (f % g)

-}


-- (map id % f == f)
-------------------------------------------------------------------
type Thing = Int

{-@ encode :: [Thing] -> [(Nat, Thing)] @-}
encode :: [Thing] -> [(Int, Thing)]
encode = map encodeBlob % group

{-@ decode :: [(Nat, a)] -> [a] @-}
decode = concat % map decodeBlob

-------------------------------------------------------------------


{-@ reflect decodeBlob @-}
{-@ decodeBlob :: (Nat, a) -> [a] @-}
decodeBlob :: (Int, a) -> [a]
decodeBlob (n, x) = replicate n x

{-@ reflect replicate @-}
{-@ replicate :: Nat -> a -> [a] @-}
replicate :: Int -> a -> [a]
replicate 0 _ = []
replicate n x = x : replicate (n-1) x

{-@ type ListNE a = {v:[a] | size v > 0} @-}

{-@ reflect encodeBlob @-}
{-@ encodeBlob :: ListNE a -> (Nat, a) @-}
encodeBlob xs = (size xs, hd xs)

{-@ reflect hd @-}
{-@ hd :: ListNE a -> a @-}
hd (x:_) = x

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0
size (x:xs) = 1 + size xs

{-@ reflect group @-}
{-@ group :: Eq a => [a] -> [ListNE a] @-}
group []     = []
group (x:xs) = (x:ys) : group zs
  where
    (ys, zs) = span x xs

{-@ reflect span @-}
{-@ span :: Eq a => a -> xs:[a] -> {v: ([a], [a]) | len (fst v) + len (snd v) == len xs && append (fst v) (snd v) == xs } @-}
span :: Eq a => a -> [a] -> ([a], [a])
span w []    =  (    [],     [])
span w (x : xs)
  | w == x    =  (x : ys,     zs)
  | otherwise =  (    [], x : xs)
  where
    (ys, zs)  = span w xs


{-@ reflect append @-}
append :: [a] -> [a] -> [a]
append []     ys = ys
append (x:xs) ys = x : append xs ys
