{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

-- Some concepts relating to measure theory.
-- Reference: https://www.math.ucdavis.edu/~hunter/m206/measure_notes.pdf
module Measures (
  Measure(algebra, fn), measure,
  volume, covers, outerMeasure, outerMeasureFn,
  caraMeasurable,
  lebesgueRd,
  lebesgueMeasure
) where

import Sets
import Functions
import Analysis
import Sequences
import Limits
import Vectors
import SigmaAlgebra

import Data.Maybe (fromJust)
import GHC.TypeLits

-------------- Measures ------------------

data Measure set w = Measure {
  algebra :: SigmaAlgebra set w,
  fn :: Fn Subset (Subset w) NonNegative ExtR1
}

measure alg fn = let candidate = Measure alg fn in
  if valid candidate then Just candidate else Nothing

instance Defined set w => Defined AllOf (Measure set w) where
  candidate _ m =
    -- Non-negativity is implied by the Fn codomain
    (events . algebra) m ⊆ (domain . fn) m &&
    -- Null empty set
    fn m ← empty == zero &&
    -- Countable additivity
    (forAll disjoints $ \sets ->
      (fn m ← unionAll sets) == (sum $ map (f $ fn m) sets))
    where disjoints = (star $ events $ algebra m) % isPairwiseDisjoint

volume m x | x ∈ (events . algebra) m = fn m ← x

-------------- Lebesgue Outer Measure ------------------

-- Used to measure the volume of sets in Rd by adding up the measures of
-- open boxes. First you need to define a box.

data Box v = Box {
  start :: v,
  end :: v
} deriving (Eq, Show)

type Interval = Box R1

-- "Before" means all elements of the first vector are l.t. the second.
before_ :: KnownNat n => RD n -> RD n -> Bool
vx `before_` vy =
  and $ map (\(x, y) -> x < y) $ zip (vecToList vx) (vecToList vy)

-- Boxes are defined with finite corners.
instance KnownNat n => Defined Box (RD n) where
  -- Contained inside a box.
  candidate box v = start box `before_` v && v `before_` end box
instance KnownNat n => Defined AllOf (Box (RD n)) where
  -- A validly constructed box.
  candidate _ box = start box `before_` end box

boxVolume_ :: KnownNat n => Fn AllOf (Box (RD n)) Positive R1
boxVolume_ = fromJust $ box $
  \b -> Vec [product $ vecToList $ end b |-| start b]

allListsOfBoxes :: KnownNat n => AllOf (Sequence AllOf (Box (RD n)))
allListsOfBoxes = everything

-- Box lists that would cover this set.
covers :: (KnownNat n, Defined set (RD n))
  => set (RD n) -> Subset (Sequence AllOf (Box (RD n)))
covers set = allListsOfBoxes % \l -> set ⊆ unionSeq l

-- The outer measure is the sum of the volumes of the tightest box cover.
outerMeasure :: (KnownNat n, Defined set (RD n)) => set (RD n) -> ExtR1
outerMeasure set = fromJust $ infimum $ smap sumVol $ covers set
  where sumVol boxes = sumSeq $ extendFn <. (boxVolume_ <. boxes)

outerMeasureFn :: KnownNat n => Fn Subset (Subset (RD n)) NonNegative ExtR1
outerMeasureFn = fromJust $ box outerMeasure

-------------- Lebesgue Measure ------------------

-- Any subset. This can be any weirdo subset that might be unmeasurable.
allSubsets :: KnownNat n => AllOf (Subset (RD n))
allSubsets = everything
 
-- By limiting the above outer measure to the set of Caratheodory measurable
-- sets, we turn the outer measure into an actual measure.
-- set and NOT set can split any subset of Rn cleanly
caraMeasurable :: (KnownNat n, Defined set (RD n)) => set (RD n) -> Bool
caraMeasurable set = forAll allSubsets $ \subset ->
  -- The outer measure doesn't have to correspond to the "volume" of the set
  -- being split, but the subject set has to make the sub-outer-measures
  -- agree with the total.
  outerMeasure subset ==
    outerMeasure (subset ∩ set) + outerMeasure (subset ∩ complement set)

-- Theorem 2.9. The collection of Carath´eodory measurable sets with respect to
-- an outer measure µ∗ is a σ-algebra, and the restriction of µ∗ to the
-- measurable sets is a measure.

-- The Lebesgue sigma-algebra, which is a strict superset of Borel sigma-algebra
-- By the power of the 
lebesgueRd :: KnownNat n => SigmaAlgebra AllOf (RD n)
lebesgueRd = fromJust $ generate everything (everything % caraMeasurable)

lebesgueMeasure :: KnownNat n => Measure AllOf (RD n)
lebesgueMeasure = fromJust $ measure lebesgueRd outerMeasureFn

-- "The" Borel measure is just the lebesgue measure limited to borel subsets.
-- Since borel is part of lebesgue this is always valid.
borelMeasure :: KnownNat n => Measure AllOf (RD n)
borelMeasure = fromJust $ measure borelRd outerMeasureFn

