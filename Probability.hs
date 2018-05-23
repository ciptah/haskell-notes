-- Probability theory in Haskell.
-- This is set-theoretic probability.
-- Random Variables will be built on top of this.

module Probability (
  ProbabilitySpace,
  Event,
  outcomes,
  events,
  probabilityMeasure,
  sum,
  isProbabilityMeasure,
  probabilitySpace,
  probability,
  conditionalProbability,
  independent,
  conditionalIndependent
) where

import Sets
import SigmaAlgebra

type Event a = Set a

data ProbabilitySpace a = ProbabilitySpace {
  outcomes :: Event a,
  events :: SigmaAlgebra a,
  probabilityMeasure :: Event a -> Double
}

probabilitySpace
    :: (Event a)
    -> (SigmaAlgebra a)
    -> (Event a -> Double)
    -> ProbabilitySpace a
probabilitySpace o f p
    | not $ isValidSigmaAlgebra o f = error "Invalid"
    | not $ isProbabilityMeasure p f = error "Invalid"
    | otherwise  = ProbabilitySpace o f p

-- A probability measure is a function defined over the sets in a σ-algebra F
-- such that... (Definition 2.4 of probability_basics.pdf)
isProbabilityMeasure :: (Event a -> Double) -> SigmaAlgebra a -> Bool
isProbabilityMeasure p f =
    (forAll (asSet f) $ \s -> p(s) >= 0)
    -- Countable additivity.
    && (forAll (allDisjoint f) $ \sets -> (p $ unionAll sets) == (sum $ map p sets))
    -- Sums to 1.
    && p (sampleSpace f) == 1.0

measurable :: ProbabilitySpace a -> (Event a) -> Bool
measurable pspace event = event `member` (asSet $ events pspace)

probability :: ProbabilitySpace a -> (Event a) -> Double
probability ps event
    | measurable ps event = (probabilityMeasure ps) event
    | otherwise = error "Invalid event for the given prob. space"

-- Given 1st event, what's probability of second event
conditionalProbability :: ProbabilitySpace a -> (Event a) -> (Event a) -> Double
conditionalProbability ps given event
    = (p $ given `intersect` event) / (p event) where p = probability ps

independent :: ProbabilitySpace a -> (Event a) -> (Event a) -> Bool
independent ps ea eb = (p ea) * (p eb) == (p $ ea `intersect` eb)
    where p = probability ps

conditionalIndependent :: ProbabilitySpace a
    -> (Event a) -> (Event a) -> (Event a) -> Bool
conditionalIndependent ps given ea eb
    = (cp ea) * (cp eb) == (cp $ ea `intersect` eb)
    where cp = conditionalProbability ps given
