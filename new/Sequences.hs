{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Sequences (
  Convergence(..), ConvRD,
  realConverges, converges, convRd, limit,
  subseq, convergentSubseq,
  foldOrdered, foldFinite, foldCountable,
  approaches, onlyFinites
) where

import GHC.TypeLits
import Data.Proxy
import Data.Maybe (isJust, fromJust)

import Sets
import Analysis
import Functions
import Vectors

-- When we talk about sequences inevitably we'll talk about convergence.
data Convergence a =
  NegInf | PosInf | Finite a deriving (Eq, Show)

instance (Defined AllOf a) => Defined AllOf (Convergence a) where
  candidate _ NegInf = True
  candidate _ PosInf = True
  candidate _ (Finite a) = valid a

-- Operations in the presence of infinity.
--   $1 - Operation
--   $2, $3 - Operands
--   $4, $5 - Result when +inf & -inf
applyOp :: (a -> a -> a) ->
  Convergence a -> Convergence a ->
  Convergence a -> Convergence a ->
  Convergence a
applyOp op (Finite x) (Finite y) _ _ = Finite $ x `op` y
-- When both operands are infinity, it's undefined (error)
applyOp op PosInf (Finite y) ip _ = ip
applyOp op (Finite y) PosInf ip _ = ip
applyOp op PosInf PosInf ip _ = ip
applyOp op NegInf (Finite y) _ im = im
applyOp op (Finite y) NegInf _ im = im
applyOp op NegInf NegInf _ im = im
-- otherwise, is undefined

-- Implement num so Convergence can be put into vectors.
instance (Num a) => Num (Convergence a) where
  c1 + c2 = applyOp (+) c1 c2 PosInf NegInf
  c1 * c2 = applyOp (*) c1 c2 PosInf NegInf
  fromInteger x = Finite (fromInteger x)
  negate (Finite x) = Finite (negate x)
  negate PosInf = NegInf
  negate NegInf = PosInf
  signum (Finite x) = Finite $ signum x
  signum PosInf = Finite $ negate 1
  signum NegInf = Finite 1
  abs (Finite x) = Finite $ abs x
  abs PosInf = PosInf
  abs NegInf = PosInf
instance (Ord a) => Ord (Convergence a) where
  (Finite x) <= (Finite y) = x < y
  PosInf <= _ = False
  _ <= PosInf = True
  NegInf <= _ = True
  _ <= NegInf = False
instance (Zero a) => Zero (Convergence a) where
  zero = Finite zero

type ConvRD n = Vector n (Convergence RealNum)

-------------- Sequence convergence ------------------
-- Use vectors, because it's more general

-- "Converges to X" (maybe not unique)
-- Definition of convergence (3.10)
-- Definition of convergence to infinity (3.12)
realConverges :: (Defined set RealNum)
  => Sequence set RealNum -> Convergence RealNum -> Bool
realConverges seq limit = let naturals = Everything :: Naturals in
  forAll (Everything :: Positive RealNum) $ \test ->
    thereExists naturals $ \bigN ->
      forAll (naturals % \n -> n > bigN) $ \n ->
        satisfy limit n test
  -- $1: type of convergence, $2: test sequence index, $3: test value
  where satisfy (Finite x) n test = (abs $ (seq ← n) - x) < test
        satisfy PosInf n test = (seq ← n) > test
        satisfy NegInf n test = (seq ← n) < -test

-- Convergence of Rd -> either pointwise or norm convergence
-- We can use pointwise
converges_ :: (KnownNat n, Defined set (RD n))
  => Proxy n -> Sequence set (RD n) -> ConvRD n -> Bool
converges_ d seq limit = let dim = natVal d in
  and $ [con i seq (limit @@ i) | i <- [0..(dim-1)] ]
  where con i seq lim = realConverges (pickFn i <. seq) lim

converges :: (KnownNat n, Defined set (RD n))
  => Sequence set (RD n) -> ConvRD n -> Bool
converges seq limit = converges_ Proxy seq limit

-- In the special case where the convergence target is all finite (or infinite)
-- We can define convergence in terms of Convergence (RD n)
toPoint_ :: KnownNat n => Proxy n -> Convergence (RD n) -> ConvRD n
toPoint_ p (Finite v) = Vec $ map (\i -> Finite $ v @@ i) $ [0..(dim v - 1)]
toPoint_ p PosInf = Vec $ repeat PosInf
toPoint_ p NegInf = Vec $ repeat NegInf

convRd :: KnownNat n => Convergence (RD n) -> ConvRD n
convRd x = toPoint_ Proxy x

-- Proposition 3.11 - Uniqueness of Convergence
-- Analyze the convergence of this sequence of reals
limit :: (Defined set (RD n), KnownNat n) =>
  Sequence set (RD n) -> Maybe (ConvRD n)
limit seq = singleton $ everything % \x -> converges seq x

-------------- Subsequences ------------------

-- There exists mapping (1 -> 4, 2 -> 9, 3 -> 16, etc.)
subseq :: (Defined set a, Eq a) => Sequence set a -> Sequence set a -> Bool
seqa `subseq` seqb = thereExists
  (Everything :: Increasing (Sequence Positive Integer)) $ \map ->
    forAll (Everything :: Positive Integer) $ \n -> seqa ← n == seqb ← map ← n

-- Bolzano-Weierstrass
-- The theorem does not claim any result about unbounded sequences (it could
-- be that they are oscillating) so the result for unbounded is undefined.
-- B-W theorem guarantees the output of this function is never empty
-- for bounded sequences
convergentSubseq :: (KnownNat n, Defined set (RD n))
  => Sequence set (RD n) -> Subset (Sequence set (RD n))
convergentSubseq seq = everything % \s -> s `subseq` seq && (isJust $ limit s)

-- Every bounded sequence has a convergent subsequence.
bolzanoWeierstrassClaim = forAll
  -- Sequence of real numbers with bounded range
  ((Everything :: AllOf (Sequence AllOf R1)) % (bounded . range)) $ \bseq ->
  convergentSubseq bseq /= empty

-------------- Folding Sets ------------------

-- Fold a countable infinite sequence.
foldOrdered :: (Defined dom a, Defined AllOf b, Eq b)
  => (a -> b -> b) -> b -> Sequence dom a -> Maybe (Sequence AllOf b)
foldOrdered fn zero sequence = box $
  \n -> let candidateb = foldr fn zero $ map (f sequence) [1..n] in
    if valid candidateb then candidateb else error "Invalid"

-- Given a (countably infinite) set, fold all values in that set according
-- to some function. This might depend on the order, so the result is the set
-- of sequence of fold results.
foldFinite :: (Eq a, Eq b, Defined set a, Defined AllOf b)
  => (a -> b -> b) -> b -> set a -> Subset b
foldFinite fn zero set | finite set =
  everything % \x -> thereExists (toList set) $
    \lst -> foldr fn zero lst == x

-- Technically toList already works for countably infinite sets, but here's
-- an alternate definition
foldCountable
  :: (Eq a, Eq b, Defined dom a, Defined (Set "All") b) =>
     (a -> b -> b) -> b -> dom a -> Subset (Sequence AllOf b)
foldCountable fn zero set | countable set = collapse $
  smap (foldOrdered fn zero) $
  mappers (Everything :: Positive Integer) set

-------------- Sequences that converge at a point ------------------
-- Useful for defining limits, which defines derivatives/integrals

approaches :: KnownNat n => ConvRD n -> Subset (Sequence AllOf (RD n))
approaches target = everything % \seq ->
  seq `converges` target &&
  forAll (Everything :: Positive Integer) ( -- Remembber this part!
    \n -> convRd (Finite (seq ← n)) /= target)

-- Filter to get only finite limits.
onlyFinites
  :: (Eq a, Defined set1 (Maybe (Convergence a)), Defined AllOf a) =>
     set1 (Maybe (Convergence a)) -> Subset a
onlyFinites subset = collapse $ smap change subset
  where change (Just (Finite x)) = Just x
        change _ = Nothing
