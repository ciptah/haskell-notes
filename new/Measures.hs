{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

-- Some concepts relating to measure theory.
-- Reference: https://www.math.ucdavis.edu/~hunter/m206/measure_notes.pdf
module Measures
  ( Measure(algebra, fn)
  , measure
  , volume
  , covers
  , outerMeasure
  , outerMeasureFn
  , caraMeasurable
  , lebesgueRd
  , lebesgueMeasure
  , sigmaFinite
  , productMeasure
  )
where

import           Sets
import           Functions
import           Analysis
import           Sequences
import           Limits
import           Vectors
import           SigmaAlgebra

import           Data.Maybe                     ( isJust
                                                , fromJust
                                                )
import           GHC.TypeLits

-------------- Measures ------------------

-- Technically this is a "measure space" because by having the sigma-algebra
-- we define the outcome set as well.
data Measure set w = Measure {
  algebra :: SigmaAlgebra set w,
  fn :: Fn Subset (Subset w) NonNegative ExtR1
} deriving Eq

measure alg fn =
  let candidate = Measure alg fn
  in  if valid candidate then Just candidate else Nothing

instance (Eq w, Defined set w) => Defined AllOf (Measure set w) where
  candidate _ m =
    valid (algebra m) && valid (fn m) &&
    -- Non-negativity is implied by the Fn codomain
    (events . algebra) m ⊆ (domain . fn) m &&
    -- Null empty set
    fn m ⬅ empty == zero &&
    -- Countable additivity
    (forAll disjoints $ \sets ->
      (fn m ⬅ unionAll sets) == (sum $ map (f $ fn m) sets))
    where disjoints = (star $ events $ algebra m) % isPairwiseDisjoint

-- Apply the measure on a set.
volume :: Defined set1 w => Measure set w -> set1 w -> ExtR1
volume m x | (algebra m) `canMeasure` ex = fn m ⬅ ex where ex = mask x

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
boxVolume_ =
  fromJust $ box $ \b -> Vec [product $ vecToList $ end b |-| start b]

allListsOfBoxes :: KnownNat n => AllOf (Sequence AllOf (Box (RD n)))
allListsOfBoxes = everything

-- Box lists that would cover this set.
covers
  :: (KnownNat n, Defined set (RD n))
  => set (RD n)
  -> Subset (Sequence AllOf (Box (RD n)))
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
  outerMeasure subset == outerMeasure (subset ∩ set) + outerMeasure
    (subset ∩ complement set)

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

-------------- Sigma-finiteness ------------------

subsetSequences
  :: Defined dom a => Measure dom a -> Subset (Sequence Subset (Subset a))
subsetSequences m =
  everything %
  -- All sets in this countable set of subsets is measurable.
               \subsetSeq -> range subsetSeq ⊆ (events . algebra) m

sigmaFinite :: Defined dom a => Measure dom a -> Bool
sigmaFinite m = thereExists (subsetSequences m) $ \subsetSeq ->
  -- All subsets in this countable unions have finite measure
  Vec [PosInf]
    ∉   (range $ volume m <<. subsetSeq)
    &&
  -- But, the union of all these sets is the total space.
        unionSeq subsetSeq
    === (outcomes . algebra) m

-------------- Product Measure ------------------

left_
  :: (Eq a, Eq b, Defined AllOf a, Defined AllOf b) => Subset (a, b) -> Subset a
left_ set = smap (\(a, b) -> a) set

right_
  :: (Eq a, Eq b, Defined AllOf a, Defined AllOf b) => Subset (a, b) -> Subset b
right_ set = smap (\(a, b) -> b) set

productMeasure
  :: (Eq a, Eq b, Defined dom1 a, Defined dom2 b)
  => Measure dom1 a
  -> Measure dom2 b
  -> Maybe (Measure Subset (a, b))
productMeasure m1 m2
  | valid m1 && valid m2 && sigmaFinite m1 && sigmaFinite m2
  =
  -- The existence of this measure is guaranteed by the Hahn–Kolmogorov
  -- theorem. The uniqueness of product measure is guaranteed only in the case
  -- that both measures are sigma-finite [Wikipedia]
    Just $ mustHave "Hahn-Kolmogorov theorem" $ measure
    (mustHave "If m1, m2 valid, this must succeed" productSa)
    (mustHave "If m1, m2 valid, thsi must succeed" productFn)
  | otherwise
  = Nothing
 where
  productFn = box $ \event -> fn m1 ⬅ left_ event * fn m2 ⬅ right_ event
  productSa = generate productOut productEv
  productEv = everything % \event ->
    -- The event is measurable only when it can be formed by taking
    -- the cartesian product of two events. NOT the same as events that
    -- can be "separated" to events in the respective measures using
    -- left_ or right_. That has MORE events than the cartesian product
    -- sigma-algebra.
    thereExists (events $ algebra $ m1) $ \ev1 ->
      thereExists (events $ algebra $ m2) $ \ev2 -> event === cartesian ev1 ev2
  productOut = cartesian (outcomes $ algebra $ m1) (outcomes $ algebra $ m2)


