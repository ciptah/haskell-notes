{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

-- Some concepts relating to measure theory.
-- Reference: https://www.math.ucdavis.edu/~hunter/m206/measure_notes.pdf
module Measures (
  Measure, measure, (←←),
  volume, covers, outerMeasure
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

volume :: KnownNat n => Box (RD n) -> R1
volume box = Vec [product $ vecToList $ end box |-| start box]

allListsOfBoxes :: KnownNat n => AllOf (Sequence AllOf (Box (RD n)))
allListsOfBoxes = everything

-- Box lists that would cover this set.
covers :: (KnownNat n, Defined set (RD n))
  => set (RD n) -> Subset (Sequence AllOf (Box (RD n)))
covers set = allListsOfBoxes % \l -> set ⊆ unionSeq l

-- The outer measure is the sum of the volumes of the tightest box cover.
outerMeasure :: (KnownNat n, Defined set (RD n)) => set (RD n) -> ExtR1
outerMeasure set = fromJust $ infimum $ smap sumVol $ covers set
  where sumVol boxes = sumSeq $ extendFn <. (volume <<. boxes)
  
