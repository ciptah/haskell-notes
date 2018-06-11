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
  Measure,
  measure, (←←)
) where

import Sets
import Functions
import Analysis
import Sequences
import Limits
import Vectors
import SigmaAlgebra

import Data.Maybe (fromJust)

-------------- Partitioning ------------------

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
partitionSequence = fromJust $ box $ partition

-------------- Measures ------------------

data Measure set w = Measure {
  algebra :: SigmaAlgebra set w,
  -- Technically this isn't correct; fn can go all the way to +inf;
  -- but the Sequences code isn't up to that task yet.
  -- Just imagine the function explodes or something
  fn :: Fn Subset (Subset w) NonNegative R1
}

measure alg fn = let candidate = Measure alg fn in
  if valid candidate then Just candidate else Nothing

instance Defined set w => Defined AllOf (Measure set w) where
  candidate _ m =
    -- Non-negativity is implied by the Fn codomain
    -- Function and algebra need to agree on what is measurable.
    (domain . fn) m == (events . algebra) m &&
    -- Null empty set
    fn m ← empty == zero &&
    -- Countable additivity
    (forAll disjoints $ \sets ->
      (fn m ← unionAll sets) == (sum $ map (f $ fn m) sets))
    where disjoints = (star $ events $ algebra m) % isPairwiseDisjoint

infixr 9 ←← -- u2190
m ←← x = fn m ← x

-------------- The Lebesgue Integral Sequence (Positive) ------------------

-- References:
-- https://en.wikipedia.org/wiki/Measure_(mathematics)
-- Shruve: https://www.springer.com/us/book/9780387401010

-- For one interval, compute the summation term
lebTerm_ :: Defined dom a
  => Measure dom a -- How to measure subsets of the domain
  -> Fn dom a NonNegative R1 -- The function to integrate
  -> Subset a -- The subset we are integrating over
  -> Subset R1 -- The range of values of the function of this sum term
  -> R1 -- The result
lebTerm_ m fn x y = yterm * pterm
  where yterm = fromJust $ infimum y :: R1
        pterm = m ←← (x ∩ (preimage fn y) ) :: R1

-- Given a list of partitions, compute the infinite sum
lebSum_ :: Defined dom a
  => Measure dom a
  -> Fn dom a NonNegative R1
  -> Subset a
  -> [Subset R1]
  -> R1
lebSum_ m fn x ys = sum $ map (lebTerm_ m fn x) ys

-- Given a sequence of ever finer partitions,
-- compute the sequence of infinite sums
lebSeq_ :: Defined dom a
  => Measure dom a
  -> Fn dom a NonNegative R1
  -> Subset a
  -> Sequence AllOf [Subset R1]
  -> Maybe (Sequence AllOf R1)
lebSeq_ m fn x seq = pure (<.) <*> boxSum <*> pure seq
  where boxSum = box $ lebSum_ m fn x
    -- :: Maybe (Fn AllOf [Subset R1] AllOf (ConvRD 1) )

-- Lebesgue integral of non-negative functions.
lebesgueP :: Defined dom a
  => Measure dom a
  -> Fn dom a NonNegative R1
  -> Subset a
  -> Maybe (ConvRD 1)
lebesgueP m fn x = coalesce $ (pure limit <*> lebSeq_ m fn x partitions)
  where partitions = (intersectWith (range fn)) <<. partitionSequence
        coalesce Nothing = Nothing
        coalesce (Just Nothing) = Nothing
        coalesce (Just (Just x)) = Just x
