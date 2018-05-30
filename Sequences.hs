-- https://www.math.ucdavis.edu/~hunter/intro_analysis_pdf/intro_analysis.pdf
-- Chapter 3

module Sequences (
  Sequence,
  nonNegativeReals,
  positiveReals,
  possibleConvergences,
  converges,
  convergence,
  order,
  toList,
  isSubsequenceOf,
  convergentSubseq
) where

import Sets
import Analysis
import Data.Maybe (Maybe, isJust, fromJust)

type Sequence a = Integer -> a

data Convergence a = NegativeInfinity | PositiveInfinity | Finite a deriving (Eq)

nonNegativeReals = reals % (\x -> x >= 0)
positiveReals = reals % (\x -> x > 0)

possibleConvergences = Everything :: Set (Convergence RealNum)

-- "Converges to X"
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

-- Whether this sequence has a pattern (increasing/decreasing/etc.)
pattern :: (Ord a) => (a -> a -> Bool) -> Sequence a -> Bool
pattern op seq = forAll naturals $ \n -> seq (n + 1) `op` seq n

strictlyIncreasing :: (Ord a) => Sequence a -> Bool
strictlyIncreasing = pattern (>)
increasing :: (Ord a) => Sequence a -> Bool
increasing = pattern (>=)
decreasing :: (Ord a) => Sequence a -> Bool
decreasing = pattern (<=)
strictlyDecreasing :: (Ord a) => Sequence a -> Bool
strictlyDecreasing = pattern (<)
monotone :: (Ord a) => Sequence a -> Bool
monotone = \seq -> increasing seq || decreasing seq
strictlyMonotone :: (Ord a) => Sequence a -> Bool
strictlyMonotone = \seq -> strictlyIncreasing seq || strictlyDecreasing seq

-------------- Application: Turning Sets into Lists -----------
--For certain sets (countable sets with totally ordered elements)
--we can define how to turn a set into a Haskell (possibly) infinite list.

-- THIS IS WRONG, because some sequences can only be monotonically decreasing.
badS :: (Ord a, Ord b) => Set a -> Set b -> Set (Boxed a b)
badS a b = mappers a b % \bf -> let f = compile bf in
  forAll (a ⨯ a) $ \(x1, x2) ->
    (x1 < x2 && f x1 < f x2) || (x1 >= x2 && f x1 >= f x2)

-- The correct way of turning a countable set to a list is finding a sequence
-- that is strictly monotone.
order :: (Ord b) => Set b -> Maybe (Sequence b)
order b = pure compile <*> singleton sequences
  where sequences = mappers naturals b % \box -> strictlyMonotone (compile box)

-- Finally, we can turn into a list those sets that have a unique sequencer.
-- With maps it's impossible to get a unique mapper, imagine swapping every
-- two indices with each other.
-- Finite sets are super easy because the inf is guaranteed to be included,
-- so we can just repeatedly build using the inf.
toList :: (Ord a) => Set a -> Maybe [a]
toList set | set == empty = Just [] -- Base case for finite case
           | isFinite set = Just $ minimum : (fromJust $ toList remainder)
           -- Apply the unique sequencer (if available) to [1..]
           | countable set = pure map <*> (order set) <*> pure [1..]
           | otherwise = Nothing
  where minimum = fromJust $ infimum set
        remainder = set `minus` singletonOf minimum

---------------- Lim Sup and Lim Inf - for every BOUNDED sequence, they exist

----------- Cauchy sequences ------------------

--------- Bolzano-Weierstrass Theorem ------------

-- There is a mapping from subsequence index to supersequence index
isSubsequenceOf :: (Eq a) => Sequence a -> Sequence a -> Bool
a `isSubsequenceOf` b = thereExists selection $ \box ->
  let mapping = compile box in forAll naturals $ \n -> a n == b (mapping n)
  where selection = (Everything :: Set (Boxed Integer Integer)) % \box ->
                    domain box == naturals && range box `isSubsetOf` naturals &&
                    strictlyIncreasing (compile box)

-- The theorem does not claim any result about unbounded sequences (it could
-- be that they are oscillating) so the result for unbounded is undefined.
-- B-W theorem guarantees the output of this function is never empty
-- for bounded sequences
convergentSubseq :: Sequence RealNum -> Set (Sequence RealNum)
convergentSubseq seq =
  Everything % \subseq ->
    subseq `isSubsequenceOf` seq && (isJust $ convergence subseq)

bolzanoWeierstrassClaim = forAll boundedSequences $ \bseq ->
  convergentSubseq bseq /= empty
  where boundedSequences = Everything % \seq -> isBounded seq
        isBounded seq = bounded $ image $ Box seq Everything
