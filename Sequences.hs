-- https://www.math.ucdavis.edu/~hunter/intro_analysis_pdf/intro_analysis.pdf
-- Chapter 3

module Sequences (
  PositiveInteger,
  Sequence,
  nonNegativeReals,
  positiveReals,
  positiveIntegers,
  possibleConvergences,
  converges,
  convergence
) where

import Sets
import Analysis
import Data.Maybe (Maybe, isJust)

type PositiveInteger = Integer -- Only an alias
type Sequence a = Integer -> a

data Convergence a = NegativeInfinity | PositiveInfinity | Finite a

nonNegativeReals = Reals % (\x -> x >= 0) :: Set RealNum
positiveReals = Reals % (\x -> x > 0) :: Set RealNum
positiveIntegers = Integers % (\x -> x > 0) :: Set Integer

possibleConvergences = (
  Singleton NegativeInfinity
  `union` Singleton PositiveInfinity
  `union` (fmap Finite Reals))

-- Definition of convergence (3.10)
-- Definition of convergence to infinity (3.12)
converges :: Sequence RealNum -> Convergence RealNum -> Bool
converges seq limit =
  forAll positiveReals $ \test ->
    thereExists positiveIntegers $ \bigN ->
      forAll (positiveIntegers % \n -> n > bigN) $ \n ->
        satisfy limit n test
  -- $1: type of convergence, $2: test sequence index, $3: test value
  where satisfy (Finite x) n test = (abs $ (seq n) - x) < test
        satisfy PositiveInfinity n test = (seq n) > test
        satisfy NegativeInfinity n test = (seq n) < -test

-- Proposition 3.11 - Uniqueness of Convergence
-- Analyze the convergence of this sequence
convergence :: Sequence RealNum -> Maybe (Convergence RealNum)
convergence seq = only $ possibleConvergences % \x -> converges seq x
  where only EmptySet = Nothing
        only (Singleton x) = Just x
        only _ = error "Impossible due to Prop 3.11"

-- A convergent sequence is always bounded. If convergent, then bounded.
-- "A sequence is bounded" is just the image of the values of the sequence.
prop319 :: Sequence RealNum -> Bool
prop319 seq = assert $ if isJust (convergence seq)
  then (bounded $ image positiveIntegers seq Reals) else True
