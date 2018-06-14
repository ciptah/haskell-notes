{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}

-- Defining the Lebesgue Integral.
module Integral (
  interval,
  partition, Partition,
  intersectWith,
  partitionSequence,

  halfOpens, mesh, intervals, integralPaths,
  finiteMeshPartitions,
  
  lebP,
  split,
  integral
) where

import Sets
import Functions
import Analysis
import Sequences
import Limits
import Vectors
import SigmaAlgebra
import Measures

-------------- Partitioning (Simple) ------------------

-- First, define a partitioning of the positive real line by taking evenly
-- sized intervals of the given size.

interval :: Integer -> R1 -> Subset R1
interval begin size = everything % \x -> let n = fromInteger begin in
  x >= n * size && x < (n + Vec [1.0]) * size

-- Partitions are countable.
partition :: Integer -> [Subset R1]
partition divisions = let sz = 1.0 / fromInteger divisions in
  map (\i -> interval i sz) [0..]

-- Intersect this partitioning with the codomain
intersectWith :: Defined set R1 => set R1 -> [Subset R1] -> [Subset R1]
intersectWith cod partition = filter (=/= empty) $ map (∩ cod) partition

-- Now define a sequence of ever-finer partitions of R+.
-- These partitions are countable, so we should define them as a sequence.
partitionSequence :: Sequence AllOf [Subset R1]
partitionSequence = mustHave "Partition works for all i >= 0" $ box $ partition

-------------- Partitioning (General) ------------------

type Partition = Sequence Subset (Subset R1)

-- Create half-open >= 0 intervals by making 1D open balls and adding the
-- infimum to the set.
halfOpens :: Subset (Subset R1)
halfOpens = smap
  (\ball -> ball ∪ singletonOf (mustHave "Reals are complete" $ infimum ball))
  (everything :: AllOf (OpenBall R1))

-- Size of the largest subpartition
mesh :: Partition -> Maybe ExtR1
mesh partition = supremum $ range $ (fn lebesgueMeasure) <. partition

-- define 0 < t1 < t2 < t3 < t4 < ...
-- The sequence doesn't have to be ordered.
intervals :: R1 -> Subset Partition
intervals maxSize = everything % \partition -> let sets = range partition in
  -- All partitions are disjoint.
  (forAll sets $ \s1 ->
    forAll (sets `minus` singletonOf s1) $ \s2 -> s1 `isDisjoint` s2) &&
  -- All partitions are half-open intervals.
  (forAll sets $ \s -> s ∈ halfOpens) &&
  -- All partitions combine into the original set.
  unionSeq partition === everything &&
  -- The largest partition size is the (finite) mesh.
  mesh partition == (Just $ extend maxSize) &&
  -- Sets start at 0.
  (forAll sets $ \s -> (mustHave "reals are complete" $ infimum s) >= zero)

-- Any partition of finite intervals.
finiteMeshPartitions = everything % \partition ->
    (thereExists (Everything :: Positive R1) $ \m -> partition ∈ intervals m)

-- Now we can define approaches to the infinitesimally small partitions.
-- Any sequence of partitions with finite mesh, the limit of which goes to 0.
-- We can also check for monotonically decreasing mesh sequence but not required.
integralPaths :: Subset (Sequence AllOf Partition)
integralPaths = everything % \seq ->
  -- Partition must be one of the intervals for some finite mesh size m.
  (forAll (range seq) $ \partition -> partition ∈ finiteMeshPartitions) &&
  lim (meshSequence seq) == (Just $ zero)
  where meshSequence seq = justMesh <<. seq
        justMesh = \part -> mustHave "already checked finiteMesh" $ mesh part


-------------- The Lebesgue Integral (Positive) ------------------

-- References:
-- https://en.wikipedia.org/wiki/Measure_(mathematics)
-- Shruve: https://www.springer.com/us/book/9780387401010

-- For one interval, compute the summation term
lebTerm_ :: Defined dom a
  => Measure dom a -- How to measure subsets of the domain
  -> Fn dom a NonNegative R1 -- The function to integrate
  -> Subset a -- The subset we are integrating over
  -> Subset R1 -- The range of values of the function of this sum term
  -> ExtR1 -- The result
lebTerm_ m fn x y = yterm * pterm
  where yterm = extend $ mustHave "y = finite interval" $ infimum y :: ExtR1
        pterm = volume m $ x ∩ (preimage fn (y ∩ range fn)) :: ExtR1

-- Given a list of partitions, compute the infinite sum
lebSum_ :: Defined dom a
  => Measure dom a
  -> Fn dom a NonNegative R1
  -> Subset a
  -> Partition
  -> ExtR1
lebSum_ m fn x ys = sumSeq $ (lebTerm_ m fn x) <<. ys

-- Given a sequence of ever finer partitions,
-- compute the sequence of infinite sums
lebSeq_ :: Defined dom a
  => Measure dom a
  -> Fn dom a NonNegative R1
  -> Subset a
  -> Sequence AllOf Partition
  -> Maybe (Sequence AllOf ExtR1)
lebSeq_ m fn x pseq = pure (<.) <*> boxSum <*> pure pseq
  where boxSum = box $ lebSum_ m fn x :: Maybe (Fn AllOf Partition AllOf ExtR1)

-- Lebesgue integral of non-negative functions
-- Along one partition scheme
lebP :: Defined dom a
  => Measure dom a -- m
  -> Fn dom a NonNegative R1 -- fn
  -> Subset a -- x
  -> Sequence AllOf Partition -- partitionSeq
  -> Maybe ExtR1
lebP m fn x partitionSeq = coalesce $ (pure lim <*> lebSeq_ m fn x partitionSeq)
  where coalesce Nothing = Nothing
        coalesce (Just Nothing) = Nothing
        coalesce (Just (Just x)) = Just x

-------------- The Lebesgue Integral (All Paths) ------------------

-- ALL PATHS must converge to the same limit.
lebPPaths :: Defined dom a
  => Measure dom a -- m
  -> Fn dom a NonNegative R1 -- fn
  -> Subset a -- x
  -> Maybe ExtR1
lebPPaths m fn x = coalesce $ singleton $ smap (lebP m fn x) integralPaths
  where coalesce Nothing = Nothing
        coalesce (Just Nothing) = Nothing
        coalesce (Just (Just x)) = Just x

-------------- The Lebesgue Integral (All Functions) ------------------

-- Split a function into Non-Negative parts.
split :: Defined dom a => Fn dom a AllOf R1
  -> (Fn dom a NonNegative R1, Fn dom a NonNegative R1)
split fn = (posFn, negFn)
  where
    stuff = mustHave "defined for all x, y >= 0" . box
    posFn = stuff $ \x -> if fn ← x > zero then fn ← x else zero
    negFn = stuff $ \x -> if fn ← x < zero then negate $ fn ← x else zero

-- int fn(.) dM over x
integral :: Defined dom a
  => Measure dom a -> Fn dom a AllOf R1 -> Subset a -> Maybe ExtR1
integral m fn x | measurable (algebra m) lebesgueRd fn  =
  if x ∈ (events . algebra) m then diff $ split fn else Nothing
  where diff (posFn, negFn) = pure (-) <*> lebPPaths m posFn x <*> lebPPaths m negFn x
integral m fn x | otherwise = Nothing
