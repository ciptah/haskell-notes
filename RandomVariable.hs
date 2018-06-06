{-# LANGUAGE ExistentialQuantification #-}

-- Random Variables
-- https://cims.nyu.edu/~cfgranda/pages/DSGA1002_fall16/material/random_variables.pdf

module RandomVariable (
  RandomVariable,
  Distribution(KnownRV, UnknownRV),
  Observation,
  RandomVariable.lookup,
  RandomVariable.apply,
  borelRd,
  makeDist,
  getRVSpace,
  getRVFunction,
  makeRV,
  (<.),
  toRV,
  pmf,
  isDiscrete,
  normal
) where

import Sets
import SigmaAlgebra
import Probability
import Analysis
import Sequences
import Series
import Vector

import Data.Maybe (fromJust, isJust)

-- We'll use the "Definition 2.1 + Remark 2.2" for this file.
-- However we'll be using the Reals as the random variable sample space
-- and the Borel sigma-algebra as the random variable events.

-- a here is the original sample space that we'll map to Real numbers.
-- Given a probability space (Ω, F, P), a random variable X is a function...
data RandomVariable a obs = RandomVariable {
  getRVSpace :: (ProbabilitySpace a),
  getRVFunction :: (a -> obs)
}

instance (Valid obs, Eq obs) => Eq (RandomVariable a obs) where
  rv1 == rv2 = (getRVSpace rv1) == (getRVSpace rv2) &&
    (Box (getRVFunction rv1) everything) == (Box (getRVFunction rv2) everything)

type Observation = RealNum

borelRd :: SigmaAlgebra obs
borelRd = error "TODO implement"

-- Given the RV, look up the set of outcomes that will be included in the
-- given observations.
lookup :: RandomVariable w obs -> Set obs -> Set w
lookup (RandomVariable space fn) selection = preimage fn selection

apply :: RandomVariable w obs -> w -> obs
apply (RandomVariable ps fn) w = fn w

-- Random variable is a function where if we take any borel subset of the
-- real line, gathered all the outcomes that map into that subset according trealso
-- the function, the set of outcomes (the inverse) we get should be a member
-- of the original probability space's sigma-algebra.
instance (Valid obs, Eq a, Eq obs) => Valid (RandomVariable a obs) where
  isValid rv =
    domain (Box fn everything) == outcomes pspace &&
    (forAllSets borelRd $ \event -> preimage fn event ∈ measurableEvents)
    where measurableEvents = measurable $ events pspace
          pspace = getRVSpace rv
          fn = getRVFunction rv

-- Distribution function is just a function from Sets of reals to the
-- probability of that set happening under the random variable.
data Distribution w obs =
  KnownRV (RandomVariable w obs)
  | UnknownRV (Set obs -> Likelihood)

instance (Eq obs) => Eq (Distribution w obs) where
  -- Distribution equality is different from random variable equality,
  -- in that they don't need to map individual w's to the same values.
  -- Aka "equality in distribution" not "probability 1"
  d1 == d2 = Box (rate d1) everything == Box (rate d2) everything

-- Construct a distribution from a function.
makeDist :: (Valid obs, Eq obs) =>
  (Set obs -> Likelihood) -> Maybe (Distribution w obs)
-- "bless" this function as a valid distribution of "some" random variable.
makeDist fn = if valid fn then Just $ UnknownRV fn else Nothing
  -- Make sure this follows all the rules of a probability measure.
  -- The easiest would be treating this as a probability measure.
  where valid fn = isProbabilityMeasure fn borelRd

-- If what we have is a function from sample to real number (which is like the
-- observed experiment value), then we construct a RV after checking its
-- validity.
makeRV :: (Valid obs, Eq a, Eq obs) =>
    ProbabilitySpace a -> (a -> obs) -> Maybe (RandomVariable a obs)
makeRV ps rv
    | isValid $ RandomVariable ps rv = Just $ RandomVariable ps rv
    | otherwise = Nothing


-- Compositions of random variables with another function.
-- Always guaranteed to generate a random variable.
(<.) :: (Valid obs2, Eq w, Eq obs2) =>
  (obs1 -> obs2) -> RandomVariable w obs1 -> RandomVariable w obs2
fn <. rv = fromJust $ makeRV (getRVSpace rv) (fn . getRVFunction rv)
infixr 9 <.

-- Invoke the probability distribution by evaluating the likelihood of an event
rate :: Distribution w obs -> Set obs -> Likelihood
rate (UnknownRV p) event = p event
rate (KnownRV (RandomVariable space rv)) event =
  -- Invoke the probability space's measure function on the set of outcomes
  -- that will generate the given set of random variable values.
  probabilityMeasure space $ preimage rv event

-- Get the underlying random variable. There's always one, but for unknown
-- RVs where we define the distribution directly this is impossible to know.
toRV :: Distribution w obs -> RandomVariable w obs
toRV (KnownRV r) = r

-- Probability mass/density functions
-- These can be defined according to the space + random variable, or
-- arbitrarily from an unknown space
pmf :: (Valid obs, Eq w, Eq obs) =>
  Distribution w obs -> Maybe (obs -> Likelihood)
-- When is a distribution discrete?
pmf (KnownRV (RandomVariable ps rv)) =
  -- A: image is a countable set and the pre-image of singleton sets are measurable
  -- https://en.wikipedia.org/wiki/Probability_distribution#Measure_theoretic_formulation
  if countable img && (forAll img $ \y -> events ps `canMeasure` preimg y)
  then Just $ \obs -> probability ps $ preimg obs
  else Nothing
  where img = image $ Box rv everything
        preimg obs = preimage rv $ singletonOf obs
pmf (UnknownRV pf) =
  -- RV can assume only a finite or countably infinite number of values.
  -- aka, there exists a countable subset of observations s.t.
  -- the sum of the singleton sets of those probabilities add up to 1.
  if thereExists everything $ \values -> -- values :: Set RealNum
    countable values && foldSum values == (singletonOf $ Just $ Finite 1.0)
  then Just $ \obs -> pf $ singletonOf obs
  else Nothing

isDiscrete :: (Valid obs, Eq w, Eq obs) => Distribution w obs -> Bool
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

-- Univariate normal.
normal :: forall w. RealNum -> RealNum -> Distribution w RealNum
normal mean var = UnknownRV $ \event -> integral (normpdf mean var) event
