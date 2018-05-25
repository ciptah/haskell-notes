-- https://www.math.ucdavis.edu/~hunter/intro_analysis_pdf/intro_analysis.pdf
-- Chapter 3

module Sequences (
  Sequence,
  nonNegativeReals,
  positiveReals,
  possibleConvergences,
  converges,
  convergence,
  sequencers,
  toList
) where

import Sets
import Analysis
import Data.Maybe (Maybe, isJust, fromJust)

type Sequence a = Integer -> a

data Convergence a = NegativeInfinity | PositiveInfinity | Finite a deriving (Eq)

nonNegativeReals = reals % (\x -> x >= 0)
positiveReals = reals % (\x -> x > 0)

possibleConvergences = Everything :: Set (Convergence RealNum)

-- Definition of convergence (3.10)
-- Definition of convergence to infinity (3.12)
converges :: Sequence RealNum -> Convergence RealNum -> Bool
converges seq limit =
  forAll positiveReals $ \test ->
    thereExists naturals $ \bigN ->
      forAll (naturals % \n -> n > bigN) $ \n ->
        satisfy limit n test
  -- $1: type of convergence, $2: test sequence index, $3: test value
  where satisfy (Finite x) n test = (abs $ (seq n) - x) < test
        satisfy PositiveInfinity n test = (seq n) > test
        satisfy NegativeInfinity n test = (seq n) < -test

-- Proposition 3.11 - Uniqueness of Convergence
-- Analyze the convergence of this sequence
convergence :: Sequence RealNum -> Maybe (Convergence RealNum)
convergence seq = singleton $ possibleConvergences % \x -> converges seq x

-- A convergent sequence is always bounded. If convergent, then bounded.
-- NOTE: not the converse: Bounded does not imply convergent.
--   HOWEVER, bounded does imply existence of convergent subsequence
--   (Bolzano-Weierstrass). Will define later.
-- "A sequence is bounded" means the image of the values of the sequence
-- is bounded.
prop319 :: Sequence RealNum -> Bool
prop319 seq = if isJust (convergence seq)
  then (bounded $ image $ Box seq Everything) else True

-- Sequencers are stronger than mappers where the mapping is guaranteed to
-- preserve order, i.e. the function is strictly monotonically increasing.
sequencers :: (Ord a, Ord b) => Set a -> Set b -> Set (Boxed a b)
sequencers a b = mappers a b % \bf -> let f = compile bf in
  forAll (a ⨯ a) $ \(x1, x2) ->
    (x1 < x2 && f x1 < f x2) || (x1 >= x2 && f x1 >= f x2)

-- Finally, we can turn into a list those sets that have a unique sequencer.
-- With maps it's impossible to get a unique mapper.
-- Finite sets are super easy because the inf is guaranteed to be included,
-- so we can just repeatedly build using the inf.
toList :: (Ord a) => Set a -> Maybe [a]
toList set | set == empty = [] -- Base case for finite case
           | isFinite set = Just $ minimum : (fromJust $ toList remainder)
           | countable set && isJust seqs = Just $ fmap seq [1..]
           | otherwise = Nothing
  where minimum = fromJust $ infimum set
        remainder = set `minus` singletonOf minimum
        seqs = singleton $ sequencers naturals set
        seq = compile $ fromJust $ seqs

