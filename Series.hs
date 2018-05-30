module Series (
  series,
  riemannZeta
) where

import Sets
import Sequences

import Data.Maybe (isJust)

-- A series is the infinite sum of the sequence, so we can represent it as
-- the partial sum sequence. Note that series requires "Num a" which is
-- different from Eq a, or Ord a that we usually use.
series :: (Num a) => Sequence a -> Sequence a
series seq 1 = seq 1
series seq n = (series seq $ n - 1) + seq n

-- This means properties like convergence, boundedness, etc. can be transferred
-- over from sequences to series.

claim4_9 = forAll realSequences $ \seq ->
  if isJust $ convergence $ series seq then seq `converges` Finite 0 else True

-- Reimann Zeta function. Only defined for 1 < s < infty, otherwise error.
riemannZeta :: RealNum -> RealNum
riemannZeta s = get limit
  where seq n = 1 / ((fromIntegral n) ** s)
        limit = convergence $ series seq
        get (Just (Finite x)) = x
