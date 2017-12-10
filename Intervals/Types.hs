{-@ LIQUID "--exact-data-con" @-}
{-@ LIQUID "--no-adt"         @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--higherorder"    @-} -- just to disable all qualifiers
{-@ LIQUID "--diff"           @-}
{- LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module Intervals.Types where

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

--------------------------------------------------------------------------------
-- | Invariant: Intervals are sorted, disjoint and non-adjacent
--------------------------------------------------------------------------------
{-@ type OrdIntervals N = [{v:Interval | N <= from v}]<{\fld v -> (to fld <= from v)}> @-}
type OrdIntervals = [Interval]

--------------------------------------------------------------------------------
-- | Invariant: Intervals start with lower-bound of 0
--------------------------------------------------------------------------------
{-@ data Intervals = Intervals { itvs :: OrdIntervals 0 } @-}
data Intervals = Intervals {itvs :: OrdIntervals } deriving (Show)

--------------------------------------------------------------------------------
-- | Invariant: Rephrased as a Haskell Predicate
--------------------------------------------------------------------------------
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

{-@ coz :: a -> () -> a @-}
coz :: a -> () -> a
coz x _ = x

--------------------------------------------------------------------------------
-- | Semantics of Intervals
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
