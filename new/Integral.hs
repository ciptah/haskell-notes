{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}

-- Defining the Lebesgue Integral.
module Integral (
  interval,
  partition,
  intersectWith,
  partitionSequence,
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

-- TODO: Non-fixed-size partitions, with a bounded maximum size

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
        pterm = volume m $ x ∩ (preimage fn y) :: ExtR1

-- Given a list of partitions, compute the infinite sum
lebSum_ :: Defined dom a
  => Measure dom a
  -> Fn dom a NonNegative R1
  -> Subset a
  -> [Subset R1]
  -> ExtR1
lebSum_ m fn x ys = sum $ map (lebTerm_ m fn x) ys

-- Given a sequence of ever finer partitions,
-- compute the sequence of infinite sums
lebSeq_ :: Defined dom a
  => Measure dom a
  -> Fn dom a NonNegative R1
  -> Subset a
  -> Sequence AllOf [Subset R1]
  -> Maybe (Sequence AllOf ExtR1)
lebSeq_ m fn x seq = pure (<.) <*> boxSum <*> pure seq
  where boxSum = box $ lebSum_ m fn x :: Maybe (Fn AllOf [Subset R1] AllOf ExtR1)

-- Lebesgue integral of non-negative functions.
lebP :: Defined dom a
  => Measure dom a
  -> Fn dom a NonNegative R1
  -> Subset a
  -> Maybe ExtR1
lebP m fn x = coalesce $ (pure lim <*> lebSeq_ m fn x partitions)
  where partitions = (intersectWith (range fn)) <<. partitionSequence
        coalesce Nothing = Nothing
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
  where diff (posFn, negFn) = pure (-) <*> lebP m posFn x <*> lebP m negFn x
integral m fn x | otherwise = Nothing
