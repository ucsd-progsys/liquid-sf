{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--higherorder"    @-} -- disable all qualifiers
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--no-termination" @-}

module Intervals.Algorithms where

import qualified Data.Set as S
import           Language.Haskell.Liquid.NewProofCombinators
import           Language.Haskell.Liquid.Prelude
import           RangeSet
import           Types

--------------------------------------------------------------------------------
-- | Intersection
--------------------------------------------------------------------------------
{-@ intersect :: x:_ -> y:_ -> {v:_ | sem v = S.intersection (sem x) (sem y)} @-}
intersect (Intervals is1) (Intervals is2) = Intervals (goI 0 is1 is2)
  where
    {-@ goI :: lb:Int -> is1:OrdIntervals lb -> is2:OrdIntervals lb ->
                 {v: OrdIntervals lb | semIs v = S.intersection (semIs is1) (semIs is2)} @-}
    goI :: Int -> OrdIntervals -> OrdIntervals -> OrdIntervals
    goI _ _ [] = []
    goI _ [] _ = []
    goI lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- reorder for symmetry
      | t1 < t2   = goI lb (i2:is2) (i1:is1)

      -- disjoint
      | f1 >= t2  = goI lb (i1:is1) is2
                      `withProof`
                         lem_disj_intervals i2 (i1:is1)
      -- subset
      | t1 == t2  = I f' t2 : goI t2 is1 is2
                      `withProof`
                          (lem_disj_intervals i2 is1 &&&
                           lem_disj_intervals i1 is2 &&&
                           lem_intersect f1 t1 f2 t2)

      -- overlapping
      | f2 < f1   = (I f' t2 : goI t2 (I t2 t1 : is1) is2)
                      `withProof`
                          (lem_split f1 t2 t1 &&&
                           lem_split f2 f1 t2 &&&
                           lem_disj_intervals (I f2 f1) (i1:is1))

      | otherwise = goI lb (I f2 t1 : is1) (i2:is2)
                      `withProof`
                          (lem_split f1 f2 t1 &&&
                           if f1 < f2 then lem_disj_intervals (I f1 f2) (i2:is2) else ())

      where f'    = mmax f1 f2

--------------------------------------------------------------------------------
-- | Union
--------------------------------------------------------------------------------
{-@ union :: x:_ -> y:_ -> {v:_ | sem v = S.union (sem x) (sem y)} @-}
union (Intervals is1) (Intervals is2) = Intervals (goU 0 is1 is2)
  where
    {-@ goU :: lb:Int -> is1:OrdIntervals lb -> is2:OrdIntervals lb ->
                 {v: OrdIntervals lb | semIs v = S.union (semIs is1) (semIs is2)} @-}
    goU :: Int -> OrdIntervals -> OrdIntervals -> OrdIntervals
    goU _ is [] = is
    goU _ [] is = is
    goU lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- reorder for symmetry
      | t1 < t2 = goU lb (i2:is2) (i1:is1)
      -- disjoint
      | f1 > t2 = i2 : goU t2 (i1:is1) is2
      -- overlapping
      | otherwise  = goU lb ( (I f' t1) : is1) is2
                        `withProof`
                            (lem_union f1 t1 f2 t2)
      where
        f' = mmin f1 f2

--------------------------------------------------------------------------------
-- | Difference
--------------------------------------------------------------------------------

{-@ subtract :: x:_ -> y:_ -> {v:_ | sem v = S.difference (sem x) (sem y)} @-}
subtract (Intervals is1) (Intervals is2) = Intervals (goS 0 is1 is2)
  where
    {-@ goS :: lb:Int -> is1:OrdIntervals lb -> is2:OrdIntervals lb ->
                 {v: OrdIntervals lb | semIs v = S.difference (semIs is1) (semIs is2)} @-}
    goS :: Int -> OrdIntervals -> OrdIntervals -> OrdIntervals
    goS _ is [] = is
    goS _ [] _  = []
    goS lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- i2 past i1
      | t1 <= f2  = (i1 : goS t1 is1 (i2:is2))
                      `withProof`
                        lem_disj_intervals i1 (i2:is2)

      -- i1 past i2
      | t2 <= f1  = (goS lb (i1:is1) is2)
                      `withProof`
                        lem_disj_intervals i2 (i1:is1)

      -- i1 contained in i2
      | f2 <= f1, t1 <= t2 = goS lb is1 (i2:is2)
                      `withProof`
                        lem_sub f1 t1 f2 t2

      -- i2 covers beginning of i1
      | f2 <= f1 = goS t2 (I t2 t1 : is1) is2
                       `withProof`
                          (lem_split f1 t2 t1 &&& lem_split f2 f1 t2 &&&
                           (if (f2 < f1) then lem_disj_intervals (I f2 f1) (i1:is1) else ()) &&&
                           lem_disj_intervals (I f1 t2) (I t2 t1 : is1))

      -- -- i2 covers end of i1
      | t1 <= t2 = ((I f1 f2) : goS f2 is1 (i2:is2))
                       `withProof`
                          (lem_split f1 f2 t1 &&&
                           lem_disj_intervals (I f1 f2) (i2 : is2) &&&
                           lem_sub f2 t1 f2 t2)

      -- i2 in the middle of i1
      | otherwise = (I f1 f2 : goS f2 (I t2 t1 : is1) is2)
                       `withProof`
                          (lem_split f1 f2 t1 &&& lem_split f2 t2 t1 &&&
                           lem_disj_intervals (I f1 f2) (i2:is2) &&&
                           lem_sub f2 t2 f2 t2 &&&
                           lem_disj_intervals i2 (I t2 t1 : is1))

-- Overhead (intersect = 9 + (union = 1) + (subtract = 15)
