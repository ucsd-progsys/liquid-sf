{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Pairs where

import Language.Haskell.Liquid.ProofCombinators

--------------------------------------------------------------------------------
-- | Pairs ---------------------------------------------------------------------
--------------------------------------------------------------------------------
data Pair = Pair Int Int

{-@ measure pFst @-}
pFst :: Pair -> Int
pFst (Pair x y) = x

{-@ measure pSnd @-}
pSnd :: Pair -> Int
pSnd (Pair x y) = y

{-@ testFst :: { pFst (Pair 3 5) == 3 } @-}
testFst = trivial

{-@ testSnd :: { pSnd (Pair 3 5) == 5 } @-}
testSnd = trivial

--------------------------------------------------------------------------------

{-@ thmSurjectivePairing ::
    n:Int -> m:Int -> { (Pair n m) == Pair (pFst (Pair n m)) (pSnd (Pair n m))}
  @-}

thmSurjectivePairing :: Int -> Int -> Proof
thmSurjectivePairing n m = trivial

{-@ thmSurjectivePairing' :: p:Pair -> { p == Pair (pFst p) (pSnd p) } @-}
thmSurjectivePairing' :: Pair -> Proof
thmSurjectivePairing' (Pair x y) = trivial

-- | swap ----------------------------------------------------------------------

{-@ reflect swapPair @-}
swapPair :: Pair -> Pair
swapPair (Pair x y) = Pair y x

{-@ thmSndFstIsSwap :: p:Pair -> { swapPair p == Pair (pSnd p) (pFst p) } @-}
thmSndFstIsSwap :: Pair -> Proof
thmSndFstIsSwap (Pair x y) = trivial

{-@ thmFstSwapIsSnd :: p:Pair -> { pFst (swapPair p) == (pSnd p) } @-}
thmFstSwapIsSnd :: Pair -> Proof
thmFstSwapIsSnd (Pair x y) = trivial
