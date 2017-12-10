{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--higherorder"    @-} -- just to disable all qualifiers
{-@ LIQUID "--diff"           @-}
{- LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module Intervals where

import qualified Data.Set as S
import           Language.Haskell.Liquid.NewProofCombinators
import           RangeSet

type Offset = Int

-- | Invariant: Intervals are non-empty
{-@ data Interval = I
      { from :: Int
      , to   :: {v: Int | from < v }
      }
  @-}
data Interval  = I
  { from :: Offset
  , to   :: Offset
  } deriving (Show)

-- | Invariant: Intervals are sorted, disjoint and non-adjacent
{-@ type OrdIntervals N = [{v:Interval | N <= from v}]<{\fld v -> (to fld <= from v)}> @-}
type OrdIntervals = [Interval]

-- | Invariant: Intervals start with lower-bound of 0
{-@ data Intervals = Intervals { itvs :: OrdIntervals 0 } @-}
data Intervals = Intervals {itvs :: OrdIntervals } deriving (Show)

-- | Invariant: Rephrased as a Haskell Predicate
{-@ okIntervals :: lb:Nat -> is:OrdIntervals lb -> {v : Bool | v } / [len is] @-}
okIntervals :: Int -> OrdIntervals -> Bool
okIntervals _ []            = True
okIntervals lb ((I f t) : is) = lb <= f && f < t && okIntervals t is

--------------------------------------------------------------------------------
-- | Unit tests
--------------------------------------------------------------------------------
okItv  = I 10 20

-- REJECTED
-- badItv = I 20 10

okItvs  = Intervals [I 10 20, I 30 40, I 40 50]

-- REJECTED
-- badItvs = Intervals [I 10 20, I 40 50, I 30 40]

--------------------------------------------------------------------------------
-- | Intersection
--------------------------------------------------------------------------------
intersect :: Intervals -> Intervals -> Intervals
intersect (Intervals is1) (Intervals is2) = Intervals (goI 0 is1 is2)
  where
    {-@ goI :: lb:Int -> is1:OrdIntervals lb -> is2:OrdIntervals lb -> OrdIntervals lb @-}
    goI :: Int -> OrdIntervals -> OrdIntervals -> OrdIntervals
    goI _ _ [] = []
    goI _ [] _ = []
    goI lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- reorder for symmetry
      | t1 < t2   = goI lb (i2:is2) (i1:is1)
      -- disjoint ::: t1 >= t2, f1 >= t2 : so i1, i2 are DISJOINT, i2 is "first", so drop it
      | f1 >= t2  = goI lb (i1:is1) is2                    -- WITH: lem_disj i2 (i1:is1)
      -- subset   ::: t1 == t2 : so i1, i2 have EQUAL-END, so intersection is `I (max f1 f2) t2`
      | t1 == t2  = I f' t2 : goI t2 is1 is2               -- WITH: lem_disj i2 is1 &&& lem_disj i1 i2s &&& lem_cap f1 t1 f2 t2
      -- overlapping
      | otherwise = goI lb ((I f1 t2) : (I t2 t1) : is1) is2  -- WITH: lem_split f1 t2 t1
      -- ORIG | otherwise = I f' t2 : go t2 ((I t2 t1) : is1) is2
      where
        f'        = mmax f1 f2

{-
  lem_cap  :: f1:_ -> t1:{_ | f1 < t1} -> f2:_ -> t2:{_ | f2 < t2 && f1 <= t2 <= t1 } ->
                { sem (I (max f1 f2) t2) = cap (sem (I f1 t1)) (sem (I f2 t2))}
  lem_split :: f:_ -> x:{_ | f < x} -> t:{_ | x < t} ->
                { sem (I f t) = cup (sem (I f x)) (sem (I x t)) }
  lem_disj  :: i:_ -> is:OrdIntervals {to i} ->
                { cap (sem i) (sem is) = empty }
  lem_cup   :: f1:_ -> t1:{_ | f1 < t1} -> f2:_ -> t2:{_ | f2 < t2 && f1 <= t2 <= t1 } ->
                { sem (I (min f1 f2) t2) = cup (sem (I f1 t1)) (sem (I f2 t2)) }
  lem_sub   :: f1:_ -> t1:{_ | f1 < t1} -> f2:_ -> t2:{_ | f2 < t2 && f2 <= f1 && t1 <= t2 } ->
                { subset (sem (I f1 t1)) (sem (I f2 t2)) }
 -}

--------------------------------------------------------------------------------
-- | Union
--------------------------------------------------------------------------------
union :: Intervals -> Intervals -> Intervals
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
      -- overlapping : f1 <= t2 <= t1
      | otherwise  = goU lb ( (I f' t1) : is1) is2
                      `coz` (lem_union f1 t1 f2 t2)
      where
        f' = mmin f1 f2

{-@ coz :: a -> () -> a @-}
coz :: a -> () -> a
coz x _ = x

--------------------------------------------------------------------------------
-- | Difference
--------------------------------------------------------------------------------
subtract :: Intervals -> Intervals -> Intervals
subtract (Intervals is1) (Intervals is2) = Intervals (goS 0 is1 is2)
  where
    {-@ goS :: lb:Int -> is1:OrdIntervals lb -> is2:OrdIntervals lb -> OrdIntervals lb @-}
    goS _ is [] = is
    goS _ [] _  = []
    goS lb (i1@(I f1 t1) : is1) (i2@(I f2 t2) : is2)
      -- i2 past i1
      | t1 <= f2 = i1 : goS t1 is1 (i2:is2)        -- WITH: lem_disj i1 (i2:is2)
      -- i1 past i2
      | t2 <= f1 = goS lb (i1:is1) is2             -- WITH: lem_dist i2 (i1:is1)
      -- i1 contained in i2
      | f2 <= f1 , t1 <= t2 = goS lb is1 (i2:is2)  -- WITH: lem_sub f1 t1 f2 t2
      -- i2 covers beginning of i1
      | f1 >= f2 = goS t2 ( (I t2 t1) : is1) is2   -- WITH: lem_cap f1 t1 f2 t2
      -- i2 covers end of i1
      | t1 <= t2 = (I f1 f2) : goS f2 is1 (i2:is2)
      -- i2 in the middle of i1
      | otherwise = I f1 f2 : goS f2 (I t2 t1 : is1) is2


--------------------------------------------------------------------------------

{-@ measure sem @-}
sem :: Intervals -> S.Set Int
sem (Intervals is) = semIs is

{-@ measure semIs @-}
semIs :: [Interval] -> S.Set Int
semIs []     = S.empty
semIs (i:is) = S.union (semI i) (semIs is)

{-@ measure semI @-}
semI :: Interval -> S.Set Int
semI (I f t) = rng f t
