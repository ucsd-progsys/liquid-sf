{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--ple"            @-}

module IndProp_Le where

import Pairs
import Peano
import Lists
import Language.Haskell.Liquid.NewProofCombinators

data SubseqProp where
  Subseq :: List -> List -> SubseqProp

data Subseq where
  SubNil  :: List -> Subseq
  SubTake :: Int -> List -> List -> Subseq -> Subseq
  SubSkip :: Int -> List -> List -> Subseq -> Subseq

{-@ data Subseq [ssNat] where
      SubNil  :: ys:List -> (SS Nil ys)
    | SubTake :: n:Int -> xs:List -> ys:List -> (SS xs ys) -> (SS (Cons n xs) (Cons n ys))
    | SubSkip :: n:Int -> xs:List -> ys:List -> (SS xs ys) -> (SS xs  (Cons n ys))
 @-}

{-@ type SS Xs Ys = Prop (Subseq Xs Ys) @-}

{-@ subseq_refl :: xs:List -> SS xs xs @-}
subseq_refl :: List -> Subseq
subseq_refl Nil         = SubNil Nil
subseq_refl (Cons x xs) = SubTake x xs xs (subseq_refl xs)


{-@ subseq_app :: l1:List -> l2:List -> l3:List
               -> pf:(SS l1 l2) -> (SS {l1} {app l2 l3}) / [ssNat pf]
  @-}
subseq_app :: List -> List -> List -> Subseq -> Subseq
subseq_app l1  l2   l3 (SubNil _)
  = SubNil (app l2 l3)
subseq_app x_l1 x_l2 l3 (SubTake x l1 l2 l1_l2)
  = SubTake x l1 (app l2 l3) (subseq_app l1 l2 l3 l1_l2)
subseq_app l1 x_l2 l3  (SubSkip x _ l2 l1_l2)
  = SubSkip x l1 (app l2 l3) (subseq_app l1 l2 l3 l1_l2)


{-@ subseq_trans :: l1:List -> l2:List -> l3:List -> SS l1 l2 -> p23:(SS l2 l3) -> (SS l1 l3) / [ssNat p23] @-}
subseq_trans :: List -> List -> List -> Subseq -> Subseq -> Subseq
subseq_trans l1   l2   l3 (SubNil _) _
  = SubNil l3
subseq_trans x_l1 x_l2 x_l3 (SubTake x l1 l2 p12) (SubTake _ _ l3 p23)
  = SubTake x l1 l3 (subseq_trans l1 l2 l3 p12 p23)
subseq_trans xl1 xl2 yl3 p12 (SubSkip y _ l3 p23)
  = SubSkip y xl1 l3 (subseq_trans xl1 xl2 l3 p12 p23)
subseq_trans l1 x_l2 x_l3 (SubSkip x _ l2 p12)    (SubTake _ _ l3 p23)
  = SubSkip x l1 l3 (subseq_trans l1 l2 l3 p12 p23)


--------------------------------------------------------------------------------
-- | Syntactic sugar for prelude -----------------------------------------------
--------------------------------------------------------------------------------
{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ impossible :: {v:a | false} -> b @-}
impossible :: a -> b
impossible _ = undefined

{-@ withPf :: x:a -> b -> {v:a | v = x} @-}
withPf :: a -> b -> a
withPf x y = x


--------------------------------------------------------------------------------
-- | Crufty termination stuff [How to auto-generate?] --------------------------
--------------------------------------------------------------------------------
{-@ measure ssNat          @-}
{-@ ssNat :: Subseq -> Nat @-}
ssNat :: Subseq -> Int
ssNat (SubNil _)        = 0
ssNat (SubTake _ _ _ p) = 1 + ssNat p
ssNat (SubSkip _ _ _ p) = 1 + ssNat p
