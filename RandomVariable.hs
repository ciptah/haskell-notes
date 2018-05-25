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
import Sequences

import Data.Maybe (fromJust)

-- We'll use the "Definition 2.1 + Remark 2.2" for this file.
-- However we'll be using the Reals as the random variable sample space
-- and the Borel sigma-algebra as the random variable events.

-- a here is the original sample space that we'll map to Real numbers.
-- Given a probability space (Ω, F, P), a random variable X is a function...
data RandomVariable a = RandomVariable (ProbabilitySpace a) (a -> RealNum)

-- Random variable is a function where if we take any borel subset of the
-- real line, gathered all the outcomes that map into that subset according to
-- the function, the set of outcomes (the inverse) we get should be a member
-- of the original probability space's sigma-algebra.
isRandomVariable :: (Eq a) => ProbabilitySpace a -> (a -> RealNum) -> Bool
isRandomVariable pspace rv =
  forAll borelSubsets $ \interval -> preimage rv interval ∈ measurableEvents
  where borelSubsets = asSet $ BorelReals :: Collection (Set RealNum)
        measurableEvents = asSet $ events pspace

randomVariable :: (Eq a) =>
    ProbabilitySpace a -> (a -> RealNum) -> RandomVariable a
randomVariable ps rv
    | isRandomVariable ps rv = RandomVariable ps rv
    | otherwise = error "Invalid RV and PSpace combo"

-- Probability mass/density functions
-- These can be defined according to the space + random variable, or
-- arbitrarily from an unknown space

-- We still retain knowledge of the original outcome types, even if they're
-- not important
data PMF a = StrictPMF (RandomVariable a) | ArbitraryPMF (RealNum -> RealNum)

getPMFFormalRV :: PMF a -> RandomVariable a
getPMFFormalRV (StrictPMF x) = x
getPMFFormalRV _ = error "Unavailable"

isPMF :: (Eq a) => PMF a -> Bool
isPMF (StrictPMF (RandomVariable ps rv)) = countable $ outcomes ps
isPMF (ArbitraryPMF pmf) = properBounds && isDiscrete && rangeSum == 1.0
  where properBounds = 0.0 ∈ lowerBounds pmfImage && 1.0 ∈ upperBounds pmfImage
        isDiscrete = countable pmfDomain
        rangeSum = foldr (+) 0 $ fromJust $ toList pmfImage
        pmfImage = range boxed
        pmfDomain = domain boxed
        boxed = Box pmf reals
