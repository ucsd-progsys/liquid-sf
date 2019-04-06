
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{- LIQUID "--diff"                                @-}

module Lists where

import Peano
import Pairs
import Language.Haskell.Liquid.ProofCombinators

--------------------------------------------------------------------------------
-- | Lists ---------------------------------------------------------------------
--------------------------------------------------------------------------------

{-@ data List [llen] @-}
data List = Nil | Cons Int List

{-@ measure llen @-}
{-@ llen :: List -> Nat @-}
llen :: List -> Int
llen Nil        = 0
llen (Cons h t) = 1 Prelude.+ llen t

-- TODO: #997
{- testllen :: { llen (Cons 1 (Cons 3 Nil)) == 2 } @-}
-- testllen = trivial

myList :: List
myList = Cons 1 (Cons 2 (Cons 3 Nil))

-- | Append---------------------------------------------------------------------

{-@ reflect app @-}
app :: List -> List -> List
app Nil         ys = ys
app (Cons x xs) ys = Cons x (app xs ys)

{-@ testApp1 :: () -> { app (Cons 1 (Cons 2 (Cons 3 Nil))) (Cons 4 (Cons 5 Nil))
                          =  Cons 1 (Cons 2 (Cons 3  (Cons 4 (Cons 5 Nil))))   } @-}
testApp1 () = trivial

{-@ testApp2 :: () -> { app Nil (Cons 4 (Cons 5 Nil)) = (Cons 4 (Cons 5 Nil))  } @-}
testApp2 () = trivial

{-@ testApp3 :: () -> { app (Cons 1 (Cons 2 (Cons 3 Nil))) Nil = Cons 1 (Cons 2 (Cons 3 Nil)) } @-}
testApp3 () = trivial

-- | Head and Tail with default ------------------------------------------------

{-@ reflect hd @-}
hd :: Int -> List -> Int
hd x Nil         = x
hd x (Cons y ys) = y

{-@ reflect tl @-}
tl :: List -> List
tl Nil         = Nil
tl (Cons x xs) = xs

{-@ testHd1 :: () -> { hd 0 (Cons 1 (Cons 2 (Cons 3 Nil))) == 1 } @-}
testHd1 () = trivial

{-@ testHd2 :: () -> { hd 0 Nil = 0} @-}
testHd2 () = trivial

{-@ testTl  :: () -> { tl (Cons 1 (Cons 2 (Cons 3 Nil))) = Cons 2 (Cons 3 Nil) } @-}
testTl () = trivial

-- | Exercises -----------------------------------------------------------------

{-@ reflect nonZeros @-}
nonZeros :: List -> List
nonZeros Nil         = Nil
nonZeros (Cons x xs) = if x /= 0
                         then Cons x (nonZeros xs)
                         else        (nonZeros xs)

{-@ testNonZeros :: () -> { nonZeros (Cons 0 (Cons 1 (Cons 0 (Cons 2 (Cons 3 (Cons 0 Nil))))))
                                    = Cons 1 (Cons 2 (Cons 3 Nil)) } @-}
testNonZeros () = trivial

{-@ reflect isOdd @-}
isOdd :: Int -> Bool
isOdd n = if n <= 0
            then False
            else if n == 1
                 then True
                 else isOdd (n Prelude.- 2)

{-@ testIsOdd  :: () -> { isOdd 13 } @-}
testIsOdd () = trivial

{-@ reflect oddMembers @-}
oddMembers :: List -> List
oddMembers Nil = Nil
oddMembers (Cons x xs) = if isOdd x
                           then Cons x (oddMembers xs)
                           else        (oddMembers xs)

{-@ testOddMembers :: () -> { oddMembers (Cons 0 (Cons 1 (Cons 0 (Cons 2 (Cons 3 (Cons 0 Nil))))))
                                        = Cons 1 (Cons 3 Nil) } @-}
testOddMembers () =  trivial

{-@ inline countOddMembers @-}
countOddMembers :: List -> Int
countOddMembers xs = llen (oddMembers xs)

-- countoddmembers [1;0;3;1;4;5] = 4.
-- countoddmembers [0;2;4] = 0.

-- TODO:see LH #997
{- testCountOddMembers
    :: { llen (oddMembers (Cons 0 (Cons 1 (Cons 0 (Cons 2 (Cons 3 (Cons 0 Nil))))))) = 2  } @-}
{-@ testCountOddMembers :: () -> { llen (oddMembers Nil) = 0  } @-}
testCountOddMembers () = trivial

{-@ reflect alternate @-}
alternate :: List -> List -> List
alternate (Cons x xs) (Cons y ys) = Cons x (Cons y (alternate xs ys))
alternate Nil         ys          = ys
alternate xs           Nil        = xs

{-@ testAlternate1 :: () -> { alternate (Cons 1 (Cons 2 Nil)) (Cons 4 (Cons 5 Nil))
                                       = Cons 1 (Cons 4 (Cons 2 (Cons 5 Nil))) }          @-}
testAlternate1 () = trivial

{-@ testAlternate2 :: () -> { alternate (Cons 1 (Cons 2 Nil)) Nil = Cons 1 (Cons 2 Nil) } @-}
testAlternate2 () = trivial

{-@ testAlternate3 :: () -> { alternate Nil (Cons 1 (Cons 2 Nil)) = Cons 1 (Cons 2 Nil) } @-}
testAlternate3 () = trivial

-- | Bags via Lists ------------------------------------------------------------

-- NOTE: flipping order to make termination easy

{-@ reflect count @-}
count :: List -> Int -> Int
count Nil         v = 0
count (Cons x xs) v = if v == x
                        then 1 + count xs v
                        else     count xs v

{- TODO #997 testCount1 :: { count (Cons 1 (Cons 2 Nil)) 1 = 1 } @-}
testCount1 =  trivial

{- TODO: #997 testCount2 :: { count (Cons 2 (Cons 1 (Cons 2 Nil))) 2 = 2 } @-}
testCount2 =  trivial

--------------------------------------------------------------------------------
-- | Reasoning about Lists -----------------------------------------------------
--------------------------------------------------------------------------------

{-@ thmNilApp :: xs:List -> { app Nil xs = xs } @-}
thmNilApp :: List -> Proof
thmNilApp xs = trivial

{-@ reflect decr @-}
decr :: Int -> Int
decr n = if n == 0 then 0 else n - 1

{-@ thmTlLenPrev :: xs:List -> { decr (llen xs) = llen (tl xs) } @-}
thmTlLenPrev :: List -> Proof
thmTlLenPrev Nil         = trivial
thmTlLenPrev (Cons x xs) = trivial

{-@ thmAppAssoc :: xs:List -> ys:List -> zs:List
                -> {app xs (app ys zs) = app (app xs ys) zs} @-}
thmAppAssoc :: List -> List -> List  -> Proof
thmAppAssoc Nil ys zs         = trivial
thmAppAssoc (Cons x xs) ys zs = trivial --thmAppAssoc xs ys zs

{-@ thmAppLen :: xs:List -> ys: List -> { llen (app xs ys) = llen xs + llen ys } @-}
thmAppLen :: List -> List -> Proof
thmAppLen Nil ys         = trivial
thmAppLen (Cons x xs) ys = thmAppLen xs ys

-- | Reverse -------------------------------------------------------------------

{-@ reflect rev @-}
rev :: List -> List
rev Nil         = Nil
rev (Cons x xs) = app (rev xs) (Cons x Nil)

{-@ testRev1 :: { rev (Cons 1 (Cons 2 (Cons 3 Nil))) = Cons 3 (Cons 2 (Cons 1 Nil)) } @-}
testRev1 = trivial

{-@ testRev2 :: { rev Nil = Nil } @-}
testRev2 = trivial

{-@ thmRevLen :: xs:List -> { llen xs = llen (rev xs) } @-}
thmRevLen :: List -> Proof
thmRevLen Nil         = trivial
thmRevLen (Cons x xs) = [ -- llen (rev (Cons x xs))
                          -- ==. llen (app (rev xs) (Cons x Nil))  ?
                          thmAppLen (rev xs) (Cons x Nil)
                          -- ==. llen (rev xs) + llen (Cons x Nil) ?
                        , thmRevLen xs
                          -- ==. llen xs + 1
                        ] *** QED

-- | List Exercises 1 ----------------------------------------------------------

{-@ thmAppNilR :: xs:List -> {app xs Nil = xs} @-}
thmAppNilR :: List -> Proof
thmAppNilR Nil         = trivial
thmAppNilR (Cons x xs) = thmAppNilR xs

{-@ thmRevAppDistr :: xs:List -> ys:List
                   -> {rev (app xs ys) = app (rev ys) (rev xs) }
  @-}
thmRevAppDistr :: List -> List -> Proof
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


{-@ thmRevInvolutive :: xs:List -> { rev (rev xs) = xs } @-}
thmRevInvolutive :: List -> Proof
thmRevInvolutive Nil
  =  trivial
thmRevInvolutive (Cons x xs)
  =  [ -- rev (rev (Cons x xs))
       -- ==. rev (app (rev xs) (Cons x Nil)) ?
       thmRevAppDistr (rev xs) (Cons x Nil)
       -- ==. app (rev (Cons x Nil)) (rev (rev xs)) ?
     , thmRevInvolutive xs
       -- ==. app (Cons x Nil) xs
       -- ==. Cons x (app Nil xs)
       -- ==. Cons x  xs
     ] *** QED

{-@  thmAppAssoc4
      :: l1:List -> l2:List -> l3:List -> l4:List ->
         { app (app (app l1 l2) l3) l4 = app l1 (app l2 (app l3 l4)) }
  @-}

thmAppAssoc4 :: List -> List -> List -> List -> Proof
thmAppAssoc4 l1 l2 l3 l4
  =  [ -- app (app (app l1 l2) l3) l4 ?
       thmAppAssoc l1 l2 l3
       -- ==. app (app l1 (app l2 l3)) l4 ?
     , thmAppAssoc l1 (app l2 l3) l4
       -- ==. app l1 (app (app l2 l3)) l4 ?
     , thmAppAssoc l2 l3 l4
       -- ==. app l1 (app l2 (app l3 l4))
     ] *** QED

-- TODO:this is silly
{-@ thmNonZerosApp :: l1:List -> l2:List ->
      { nonZeros (app l1 l2) = app (nonZeros l1) (nonZeros l2) }
  @-}
thmNonZerosApp :: List -> List -> Proof
thmNonZerosApp (Cons x xs) l2
  | x == 0            = thmNonZerosApp xs l2
  | x /= 0            = thmNonZerosApp xs l2
thmNonZerosApp Nil l2 = trivial

-- | List Equality -------------------------------------------------------------

{-@ reflect beqList @-}
beqList :: List -> List -> Bool
beqList (Cons x xs) (Cons y ys) = x == y && beqList xs ys
beqList Nil         Nil         = True
beqList Nil         (Cons y ys) = False
beqList (Cons x xs) Nil         = False

{-@ testBeqList1 :: () -> { beqList Nil Nil } @-}
testBeqList1 () = trivial

{- TODO:#997 testBeqList2 :: { beqList (Cons 1 Nil) (Cons 1 Nil) } @-}
testBeqList2 = trivial

{- TODO:#997 testBeqList3 :: { beqList (Cons 1 (Cons 2 Nil)) (Cons 1 (Cons 3 Nil)) == False } @-}
testBeqList3 = trivial

{-@ thmBeqListRefl :: xs:List -> {beqList xs xs} @-}
thmBeqListRefl :: List -> Proof
thmBeqListRefl Nil          = trivial
thmBeqListRefl (Cons x xs)  = thmBeqListRefl xs

{-@ thmRevInjective :: xs:List -> ys:List -> { rev xs = rev ys => xs = ys } @-}
thmRevInjective :: List -> List -> Proof
thmRevInjective xs ys
  = [ thmRevInvolutive xs
    , thmRevInvolutive ys
    ] *** QED


-- | Options -------------------------------------------------------------------

{- data Option = None | Some Int @-}
data Option = None | Some Int

-- | Partial Maps -------------------------------------------------------------

type Key = Int
type Val = Int

{-@ data Map [mlen] @-}
data Map = Empty | Record Key Val Map

{-@ measure mlen @-}
{-@ mlen :: Map -> Nat @-}
mlen :: Map -> Int
mlen Empty          = 0
mlen (Record k v r) = 1 + (mlen r)

{-@ reflect update @-}
update :: Map -> Key -> Val -> Map
update m k v = Record k v m

{-@ reflect find @-}
find :: Map -> Key -> Option
find Empty          key = None
find (Record k v r) key
  | k == key            = Some v
  | otherwise           = find r key

{-@ thmUpdateEq :: d:Map -> k:Key -> v:Val ->
      { find (update d k v) k = Some v }
  @-}
thmUpdateEq :: Map -> Key -> Val -> Proof
thmUpdateEq d k v = trivial

{-@ thmUpdateNeq :: d:Map -> k1:Key -> k2:{Key | k2 /= k1} -> v:Val ->
      { find (update d k2 v) k1 = find d k1 }
  @-}
thmUpdateNeq :: Map -> Key -> Key -> Val -> Proof
thmUpdateNeq d k1 k2 v' = trivial
