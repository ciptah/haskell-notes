-- Limits and continuity
module Limits (
  isLimit,
  seqTo,
  seqDim,
  seqToVec,
  limit,
  continuousAtR,
  continuousAt
) where

import Sets
import Analysis
import Sequences
import Vector

import Data.Maybe
import Data.Proxy
import GHC.TypeLits

-- Definition 6.1
-- requirement of a limit (1D)
--
approaches_ :: (RealNum -> RealNum) -> RealNum -> RealNum -> Bool
approaches_ fn c l = let bfn = Box fn Everything in
  forAll (Everything % (> 0)) $ \epsilon ->
    thereExists (Everything % (> 0)) $ \delta ->
      forAll Everything $ \x -> let absxc = abs $ x - c in
        if absxc > 0 && absxc < delta && x ∈ (domain bfn)
        then (abs $ fn x - l) < epsilon
        else True

isAccumulationPoint fn c = error "TODO"

-- isLimit fn a b = lim (x -> a) fn x = b
-- Technically isLimit requires that c be an accumulation point
-- (for example isolated points are not accumulated points)
isLimit fn c l = isAccumulationPoint fn c && approaches_ fn c l

-- To find the limit of functions Rn -> R, use the "all paths" definition.

-- Set of all sequences that converge to some real number.
seqTo :: RealNum -> Set (Sequence RealNum)
seqTo x = Everything % \seq -> convergence seq == (Just $ Finite x)

seqDim :: (KnownNat n) => Sequence (RealD n) -> Int -> Sequence RealNum
seqDim seq d = (@@ d) . seq

-- Set of all multivariate sequences that converge to some point.
seqToVec :: (KnownNat n) => RealD n -> Set (Sequence (RealD n))
seqToVec vx = seqToVec_ vx Proxy

seqToVec_ :: (KnownNat n) => RealD n -> Proxy n -> Set (Sequence (RealD n))
seqToVec_ vx n = Everything % \seq -> and [
  convergence (seqDim seq d) == (Just $ Finite $ vx @@ d)
  | d <- map fromIntegral [0..((natVal n) - 1)] ]

-- Proposition 6.3. The limit of a function is unique if it exists
limit :: (KnownNat n) =>
  (RealD n -> RealNum) -> RealD n -> Maybe (Convergence RealNum)
limit fn c | isAccumulationPoint fn c =
  coalesce $ singleton $ smap limitPath (seqToVec c)
  where limitPath seq = (convergence $ fn . seq) -- :: (Maybe (Convergence R))
        -- Nothing: not unique (different paths arrive at different limits)
        -- Just Nothing: unique, but does not converge
        -- Just Just: Unique, defined limit
        -- Just Just Finite x: Unique, finite convergence
        coalesce Nothing = Nothing
        coalesce (Just x) = x

using = error "Undefined"

continuousAtR fn c
  | using == "General definition" = approaches_ fn c (fn c)

continuousAt fn c
  | using == "Limit definition" && isAccumulationPoint fn c =
    limit fn c == (Just $ Finite $ fn c)

