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

type PositiveInteger = Word -- Only an alias
type Sequence a = PositiveInteger -> a

data Convergence a = NegativeInfinity | PositiveInfinity | Finite a

nonNegativeReals = reals % (\x -> x >= 0) :: Set RealNum
positiveReals = reals % (\x -> x > 0) :: Set RealNum
positiveIntegers = fmap fromIntegral $ integers % (\x -> x > 0) :: Set PositiveInteger

possibleConvergences = (
  Singleton NegativeInfinity
  `union` Singleton PositiveInfinity
  `union` (fmap Finite reals))

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
-- NOTE: not the converse: Bounded does not imply convergent.
--   HOWEVER, bounded does imply existence of convergent subsequence
--   (Bolzano-Weierstrass). Will define later.
-- "A sequence is bounded" means the image of the values of the sequence
-- is bounded.
prop319 :: Sequence RealNum -> Bool
prop319 seq = assert $ if isJust (convergence seq)
  then (bounded $ image positiveIntegers seq reals) else True
