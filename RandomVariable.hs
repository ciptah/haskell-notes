{-# LANGUAGE ExistentialQuantification #-}

-- Random Variables
-- https://cims.nyu.edu/~cfgranda/pages/DSGA1002_fall16/material/random_variables.pdf

module RandomVariable (
  RandomVariable,
  Observation,
  Distribution(KnownRV),
  makeDist,
  isRandomVariable,
  makeRV,
  toRV,
  pmf,
  isDiscrete
) where

import Sets
import SigmaAlgebra
import Probability
import Analysis
import Sequences

import Data.Maybe (fromJust, isJust)

-- We'll define aliases to distinguish against Observation.
type Observation = RealNum -- values emitted by the random variable.

-- We'll use the "Definition 2.1 + Remark 2.2" for this file.
-- However we'll be using the Reals as the random variable sample space
-- and the Borel sigma-algebra as the random variable events.

-- a here is the original sample space that we'll map to Real numbers.
-- Given a probability space (Ω, F, P), a random variable X is a function...
data RandomVariable a = RandomVariable (ProbabilitySpace a) (a -> Observation)

-- Random variable is a function where if we take any borel subset of the
-- real line, gathered all the outcomes that map into that subset according to
-- the function, the set of outcomes (the inverse) we get should be a member
-- of the original probability space's sigma-algebra.
isRandomVariable :: (Eq a) => ProbabilitySpace a -> (a -> Observation) -> Bool
isRandomVariable pspace rv = domain (Box rv reals) == outcomes pspace &&
  (forAllSets borelR $ \event -> preimage rv event ∈ measurableEvents)
  where measurableEvents = measurable $ events pspace

-- Distribution function is just a function from Sets of reals to the
-- probability of that set happening under the random variable.
data Distribution w =
  KnownRV (RandomVariable w) | UnknownRV (Set Observation -> Likelihood)

-- Construct a distribution from a function.
makeDist :: (Set Observation -> Likelihood) -> Maybe (Distribution w)
-- "bless" this function as a valid distribution of "some" random variable.
makeDist fn = if valid fn then Just $ UnknownRV fn else Nothing
  -- Make sure this follows all the rules of a probability measure.
  -- The easiest would be treating this as a probability measure.
  where valid fn = isProbabilityMeasure fn borelR

-- If what we have is a function from sample to real number (which is like the
-- observed experiment value), then we construct a RV after checking its
-- validity.
makeRV :: (Eq a) =>
    ProbabilitySpace a -> (a -> Observation) -> Maybe (RandomVariable a)
makeRV ps rv
    | isRandomVariable ps rv = Just $ RandomVariable ps rv
    | otherwise = Nothing

-- Invoke the probability distribution by evaluating the likelihood of an event
rate :: Distribution w -> Set Observation -> Likelihood
rate (UnknownRV p) event = p event
rate (KnownRV (RandomVariable space rv)) event =
  -- Invoke the probability space's measure function on the set of outcomes
  -- that will generate the given set of random variable values.
  probabilityMeasure space $ preimage rv event

-- Get the underlying random variable. There's always one, but for unknown
-- RVs where we define the distribution directly this is impossible to know.
toRV :: Distribution w -> RandomVariable w
toRV (KnownRV r) = r

-- Probability mass/density functions
-- These can be defined according to the space + random variable, or
-- arbitrarily from an unknown space
pmf :: (Eq w) => Distribution w -> Maybe (Observation -> Likelihood)
-- When is a distribution discrete?
pmf (KnownRV (RandomVariable ps rv)) =
  -- A: image is a countable set and the pre-image of singleton sets are measurable
  -- https://en.wikipedia.org/wiki/Probability_distribution#Measure_theoretic_formulation
  if countable img && (forAll img $ \y -> events ps `canMeasure` preimg y)
  then Just $ \obs -> probability ps $ preimg obs
  else Nothing
  where img = image $ Box rv Everything
        preimg obs = preimage rv $ singletonOf obs
pmf (UnknownRV pf) =
  -- RV can assume only a finite or countably infinite number of values.
  -- aka, there exists a countable subset of observations s.t.
  -- the sum of the singleton sets of those probabilities add up to 1.
  if thereExists (Everything :: Collection (Set Observation)) $ \values ->
    countable values &&
    1.0 == (sum $ map (\v -> pf $ singletonOf v) $ fromJust $ toList values)
  then Just $ \obs -> pf $ singletonOf obs
  else Nothing

isDiscrete :: (Eq w) => Distribution w -> Bool
isDiscrete dist = isJust $ pmf dist

---------------------- Some Distributions ------------------

-- Quick declaration of a 1-D integral.
-- We'll work on deriving this later.
integral :: (RealNum -> RealNum) -> Set RealNum -> RealNum
integral density domain = error "magic!"

-- Density function of the distribution.
normpdf :: RealNum -> RealNum -> RealNum -> RealNum
normpdf mean var x =
  1.0 / (sqrt $ 2 * pi * var) * (exp $ - (x - mean) ** 2 / 2 / var)

normal :: forall w. Observation -> Observation -> Distribution w
normal mean var = UnknownRV $ \event -> integral (normpdf mean var) event
