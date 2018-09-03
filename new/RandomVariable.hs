{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

-- Random Variables
-- https://cims.nyu.edu/~cfgranda/pages/DSGA1002_fall16/material/random_variables.pdf

-- Technically random variables are just functions that go from the outcome set
-- to a real number. In this code random variables are Functions attached to
-- a probability space.

module RandomVariable
  ( RandomVector(underlyingSpace, deterministicFn)
  , RandomVariable
  , allRandomVectors
  , toRandomVector
  , rvPreimage
  , rvSelect
  , rvPick
  , rvCompose
  , Distribution
  , distribution
  , expectation
  , expectedComponent
  , mean
  , distCompose
  )
where

import           Probability
import           Vectors
import           Sets
import           Functions
import           Measures
import           Sequences
import           SigmaAlgebra
import           Integral
import           Data.Proxy
import           GHC.TypeLits
import           Data.Maybe                     ( fromJust )

-------------------------- Random Vectors ---------------------------

data RandomVector (dim :: Nat) set w = RandomVector {
  underlyingSpace :: ProbabilitySpace set w,
  deterministicFn :: Fn set w AllOf (RD dim) -- NOT ExtRD!
} deriving Eq

type RandomVariable set w = RandomVector 1 set w

-- For a constructed random vector to be valid,
-- the function domain and the outcome set of the probability space must agree.
-- Also all borel subsets of the image must be measurable.
instance (KnownNat dim, Defined set w, Eq w) => Defined AllOf (RandomVector dim set w) where
  candidate _ (RandomVector space fn) = (outcomes . algebra . asMeasure) space === domain fn && measurable (algebra $ asMeasure space) borelRd fn

-- All valid random variables of the given domain.
allRandomVectors
  :: (KnownNat dim, Defined set w, Eq w) => AllOf (RandomVector dim set w)
allRandomVectors = Everything

-- Package a probability space and function into a random variable.
toRandomVector
  :: (KnownNat dim, Eq w, Defined set w)
  => ProbabilitySpace set w
  -> Fn set w AllOf (RD dim)
  -> Maybe (RandomVector dim set w)
toRandomVector ps fn = if rv ∈ allRandomVectors then Just rv else Nothing
  where rv = RandomVector ps fn

-- Given the RV, look up the set of outcomes that will be included in the
-- given observations.
rvPreimage
  :: (KnownNat dim, Defined dom w, Defined set (RD dim))
  => RandomVector dim dom w
  -> set (RD dim)
  -> Subset w
rvPreimage rv target | borelRd `canMeasure` target =
  preimage (deterministicFn rv) target

-- Apply the "vector selection" operator to the random vector.
rvSelect
  :: (KnownNat dim, KnownNat n, Defined dom a2, Eq a2)
  => Selection dim n
  -> RandomVector n dom a2
  -> RandomVector dim dom a2
rvSelect sel rv = fromJust
  $ toRandomVector (underlyingSpace rv) (stripFn sel (deterministicFn rv))

-- Pick one component of the random vector as a random variable.
rvPick
  :: (KnownNat dim, Defined dom a2, Eq a2)
  => Integer
  -> RandomVector dim dom a2
  -> RandomVariable dom a2
rvPick d rv = rvSelect (fromJust $ sel [d]) rv

-- Composition of a RV with another function yields another RV.
rvCompose
  :: (KnownNat dim1, KnownNat dim2, Defined dom a, Eq a)
  => Fn AllOf (RD dim1) AllOf (RD dim2)
  -> RandomVector dim1 dom a
  -> RandomVector dim2 dom a
rvCompose fn rv | borelMeasurable fn =
  fromJust $ toRandomVector (underlyingSpace rv) (fn <. deterministicFn rv)

-------------------------- Distributions ---------------------------

-- At its core a Distribution is basically a Probability Space where the
-- outcomes are the results of the random variable and the sigma-algebra is the
-- borel sigma algebra.

-- Create an alias.
type Distribution (dim :: Nat) = ProbabilitySpace AllOf (RD dim)

-- Get the distribution of the random variable.
distribution
  :: (KnownNat n, Eq w, Defined dom w) => RandomVector n dom w -> Distribution n
distribution rv | rv ∈ allRandomVectors =
  fromJust
    $ asProbabilitySpace
    $ fromJust
    $ measure
    -- This must apply for all borel sets (that is any set of real vectors that
    -- can be generated from countable union, intersection)
        borelRd
        ( fromJust
        $ box
        $ \rset ->
      -- The probability of a set of RV observations is the probability
      -- of the preimage of that set wrt the original probability space.
                   probability (underlyingSpace rv) (rvPreimage rv rset)
        )

-- Because distributions are measures, the expectation operation can be
-- thought of as a Lebesgue integral int f dP over all real vectors.
expectation
  :: (KnownNat n) => Distribution n -> Fn AllOf (RD n) AllOf R1 -> ExtR1
expectation dist fn = fromJust
  $ integral (asMeasure dist) fn (mask $ outcomes $ algebra $ asMeasure dist)

-- Expected value of a component of the distribution.
expectedComponent :: KnownNat n => Distribution n -> Integer -> ExtR1
expectedComponent dist d = expectation dist (selFn $ fromJust $ sel [d])

dim_ :: (KnownNat n) => Proxy n -> Distribution n -> Integer
dim_ proxy _ = natVal proxy

-- Expected vector of the distribution.
mean :: KnownNat n => Distribution n -> Vector n ExtR1
mean dist = Vec $ map (expectedComponent dist) [1 .. (dim_ Proxy dist)]

-- Composition of a distribution to another distribution. Basically
-- "masking" the outcome of the original random variable.
-- It's not the same as composing the original random variable because we don't
-- need to remember the original set.
--
-- This is not a generic probability space composition function. To create
-- something like that we need to pass in a function and a sigma-algebra
-- instead of a function that we require to be borel measurable
distCompose
  :: (KnownNat n, KnownNat m)
  => Fn AllOf (RD m) AllOf (RD n)
  -> Distribution m
  -> Distribution n
distCompose fn dist | borelMeasurable fn =
  distribution $ fromJust $ toRandomVector dist fn

-- Since distributions are probability spaces one can turn it back to a
-- random variable using an identity function. However this is NOT the same
-- random variable that generated the distribution originally (the one with
-- "set w"). Many RVs can have the same distribution but completely different
-- outcome sets.

-------------------------- PMF and PDF ---------------------------

-- COMING SOON
