-- Random Variables
-- https://cims.nyu.edu/~cfgranda/pages/DSGA1002_fall16/material/random_variables.pdf

module RandomVariable (
  RandomVariable,
  isRandomVariable
) where

import Sets
import SigmaAlgebra
import Probability

-- We'll use the "Definition 2.1 + Remark 2.2" for this file.
-- However we'll be using the Reals as the random variable sample space
-- and the Borel sigma-algebra as the random variable events.

-- a here is the original sample space that we'll map to Real numbers.
-- Given a probability space (Ω, F, P), a random variable X is a function...
data RandomVariable a = RandomVariable (ProbabilitySpace a) (a -> Double)

-- Transform the given set of real values into a set of outcomes
-- using the inverse of the given function from outcome to Real
invert :: Set a -> (a -> Double) -> Set Double -> Set a
invert outcomes rv interval =
    let omega = asList outcomes
        filteredOutcomes = filter (\w -> rv w `member` interval) omega
    in fromList filteredOutcomes

-- Random variable is a function where if we take any borel subset of the
-- real line, gathered all the outcomes that map into that subset according to
-- the function, the set of outcomes (the inverse) we get should be a member
-- of the original probability space's sigma-algebra.
isRandomVariable :: ProbabilitySpace a -> (a -> Double) -> Bool
isRandomVariable pspace rv =
  forAll borelSubsets $ \interval -> (inverseOf interval) `member` originalF
  where borelSubsets = asSet $ BorelReals :: Collection (Set Double)
        originalF = asSet $ events pspace
        inverseOf interval = invert (outcomes pspace) rv interval
