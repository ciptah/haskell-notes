-- Random Variables
-- https://cims.nyu.edu/~cfgranda/pages/DSGA1002_fall16/material/random_variables.pdf

module RandomVariable (
  RandomVariable,
  isRandomVariable,
  randomVariable
) where

import Sets
import SigmaAlgebra
import Probability
import Analysis

-- We'll use the "Definition 2.1 + Remark 2.2" for this file.
-- However we'll be using the Reals as the random variable sample space
-- and the Borel sigma-algebra as the random variable events.

-- a here is the original sample space that we'll map to Real numbers.
-- Given a probability space (Ω, F, P), a random variable X is a function...
data RandomVariable a = RandomVariable (ProbabilitySpace a) (a -> Double)

-- Random variable is a function where if we take any borel subset of the
-- real line, gathered all the outcomes that map into that subset according to
-- the function, the set of outcomes (the inverse) we get should be a member
-- of the original probability space's sigma-algebra.
isRandomVariable :: (Eq a) => ProbabilitySpace a -> (a -> Double) -> Bool
isRandomVariable pspace rv =
  forAll borelSubsets $ \interval -> (inverseOf interval) `member` originalF
  where borelSubsets = asSet $ BorelReals :: Collection (Set Double)
        originalF = asSet $ events pspace
        inverseOf interval = preimage (outcomes pspace) rv interval

randomVariable :: (Eq a) =>
    ProbabilitySpace a -> (a -> Double) -> RandomVariable a
randomVariable ps rv
    | isRandomVariable ps rv = RandomVariable ps rv
    | otherwise = error "Invalid RV and PSpace combo"

-- Probability mass/density functions
-- These can be defined according to the space + random variable, or
-- arbitrarily from an unknown space

-- We still retain knowledge of the original outcome types, even if they're
-- not important
data PMF a = StrictPMF (RandomVariable a) | ArbitraryPMF (Double -> Double)

getPMFFormalRV :: PMF a -> RandomVariable a
getPMFFormalRV (StrictPMF x) = x
getPMFFormalRV _ = error "Unavailable"

-- (Wikipedia) "a measurable space whose underlying σ-algebra is discrete..."
isDiscrete :: SigmaAlgebra a -> Bool
isDiscrete = error "Not implemented"

isDiscreteFn :: (Double -> Double) -> Bool
isDiscreteFn = error "Not implemented"

-- TODO: There's a better definition here that involves support,
-- replace this after reviewing
isPMF :: PMF a -> Bool
isPMF (StrictPMF (RandomVariable ps rv)) = isDiscrete (events ps)
isPMF (ArbitraryPMF pmf) = -- Shortcut when the RV isn't known.
    isDiscreteFn pmf && (forAll Reals $ \x -> pmf x >= 0 && x <= 1.0)
    && (sum $ map pmf (asList Reals)) == 1.0
