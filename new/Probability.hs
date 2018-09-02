{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Probability (
  Probability,
  ProbabilitySpace(asMeasure),
  allProbabilitySpaces,
  asProbabilitySpace,
  probability,
) where

import Sets
import SigmaAlgebra
import Measures
import Vectors
import Sequences
import Data.Maybe

-- Probability spaces are measure spaces such that the measure of the whole
-- space is equal to 1.

type Probability = Set "Probability"

-- The set of measures on set w that are probability measures.
instance (Defined set w, Eq w) => Defined Probability (Measure set w) where
  candidate _ ps = (Vec [Finite 1.0]) == volume ps (mask $ outcomes $ algebra $ ps)

-- A "blessed" probability space whose measure is a probability measure
data ProbabilitySpace set w = ProbabilitySpace {
  asMeasure :: Measure set w
}

allProbabilitySpaces :: (Defined set w) => Probability (Measure set w)
allProbabilitySpaces = Everything

-- "Bless" a measure into a probability space.
asProbabilitySpace :: (Eq w, Defined set w) => Measure set w -> Maybe (ProbabilitySpace set w)
asProbabilitySpace ms
  | ms ∈ allProbabilitySpaces = Just $ ProbabilitySpace ms
  | otherwise = Nothing

probability :: Defined set1 w => ProbabilitySpace set w -> set1 w -> ExtR1
probability ps event = volume (asMeasure ps) event

conditionalProbability
  :: (Defined set1 w, Defined set2 w) =>
     ProbabilitySpace set w -> set1 w -> set2 w -> a
conditionalProbability ps given event
    = (probability ps $ given `intersect` event) // (probability ps given)
    where (//) x y = error "TODO Force Real Division"

independent ps ea eb = (probability ps ea) * (probability ps eb) == (probability ps $ ea `intersect` eb)
