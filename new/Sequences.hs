{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Sequences (
  ExtR(..), ExtRD, ExtR1, justFinite,
  realConverges, converges, extend, extendFn, lim,
  subseq, convergentSubseq,
  foldOrdered, foldFinite, foldCountable,
  approaches, stripe, seqTail,
  limSup, limInf,
  series, sumSeq, unionSeq
) where

import GHC.TypeLits
import Data.Proxy
import Data.Maybe (isJust)

import Sets
import Analysis
import Functions
import Vectors

-- When we talk about sequences inevitably we'll talk about convergence.
data ExtR =
  NegInf | PosInf | Finite RealNum deriving (Eq, Show)

instance Defined AllOf ExtR where
  candidate _ NegInf = True
  candidate _ PosInf = True
  candidate _ (Finite a) = valid a

-- Operations in the presence of infinity.
--   $1 - Operation
--   $2, $3 - Operands
--   $4, $5 - Result when +inf & -inf
applyOp :: (RealNum -> RealNum -> RealNum) ->
  ExtR -> ExtR ->
  ExtR -> ExtR ->
  ExtR
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
instance Num (ExtR) where
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
instance Ord (ExtR) where
  (Finite x) <= (Finite y) = x < y
  PosInf <= _ = False
  _ <= PosInf = True
  NegInf <= _ = True
  _ <= NegInf = False
instance Zero (ExtR) where
  zero = Finite zero

type ExtRD n = Vector n ExtR
type ExtR1 = ExtRD 1
instance Complete (ExtRD 1) where

justFinite :: Maybe ExtR1 -> Bool
justFinite (Just v) = v @@ 0 /= PosInf && v @@ 0 /= NegInf
justFinite _ = False

-------------- Extend a vector into the extended real space ------------------

extend :: KnownNat n => RD n -> ExtRD n
extend x = Vec $ map Finite $ vecToList x

extendFn :: (Defined set (RD n), KnownNat n) => Fn set (RD n) AllOf (ExtRD n)
extendFn = mustHave "ExtRD contains RD" $ box extend -- Guaranteed success

-------------- Break apart a vector sequence. ------------------

stripe_ :: (Zero dat, Defined set (Vector n dat), Defined AllOf dat, KnownNat n)
  => Proxy n -> Sequence set (Vector n dat) -> [Sequence AllOf dat]
stripe_ proxy vseq =
  map (\d -> pickFn d <. vseq) [0..(fromIntegral (natVal proxy) - 1)]

stripe :: (Zero dat, Defined set (Vector n dat), Defined AllOf dat, KnownNat n)
  => Sequence set (Vector n dat) -> [Sequence AllOf dat]
stripe vseq = stripe_ Proxy vseq

-------------- Sequence convergence ------------------
-- Use vectors, because it's more general

-- "Converges to X" (maybe not unique)
-- Definition of convergence (3.10)
-- Definition of convergence to infinity (3.12)
realConverges :: (Defined set RealNum) => Sequence set RealNum -> ExtR -> Bool
realConverges seq limit = let naturals = Everything :: Naturals in
  forAll (Everything :: Positive RealNum) $ \test ->
    thereExists naturals $ \bigN ->
      forAll (naturals % \n -> n > bigN) $ \n ->
        satisfy limit n test
  -- $1: type of convergence, $2: test sequence index, $3: test value
  where satisfy (Finite x) n test = (abs $ (seq ⬅ n) - x) < test
        satisfy PosInf n test = (seq ⬅ n) > test
        satisfy NegInf n test = (seq ⬅ n) < -test

-- Convergence of Rd -> either pointwise or norm convergence
-- We can use pointwise
converges_ :: (KnownNat n, Defined set (RD n))
  => Proxy n -> Sequence set (RD n) -> ExtRD n -> Bool
converges_ d seq limit = let dim = natVal d in
  and $ [con i seq (limit @@ i) | i <- [0..(dim-1)] ]
  where con i seq lim = realConverges (pickFn i <. seq) lim

converges :: (KnownNat n, Defined set (RD n))
  => Sequence set (RD n) -> ExtRD n -> Bool
converges seq limit = converges_ Proxy seq limit

-------------- Convergence (#2) ------------------

-- Using lim sup and lim inf, and makes it work for Sequence set (ExtRD n)
-- The intuition behind lim sup/lim inf is a "shrink wrap" on the sequence,
-- that hides all the directional changes and makes the convergence
-- easily visible.

-- tail :: Sequence set a -> Integer -> Sequence set a
-- n = how many entries to skip
seqTail :: (Eq b, Defined cod b) => Sequence cod b -> Integer -> Sequence cod b
seqTail seq n = mustHave "Only changing the index" $ box $ \m -> seq ⬅ (m + n)

-- lim sup/lim inf on a given dimension.
-- a supremum or infimum always exists.
seqDim_ :: Defined set ExtR
  => String -> Sequence set ExtR -> Sequence AllOf ExtR
seqDim_ limType seq = mustHave "Section 3.6: Always exists" $ box $
  \n -> mustHave "lim sup/inf" $ extremum $ range $ seqTail seq (n - 1)
  where extremum = if limType == "supremum" then supremum else infimum

limitDim_ :: Defined set ExtR => String -> Sequence set ExtR -> ExtR
limitDim_ limType seq =
  -- lim sup will only decrease while lim inf will only increase.
  -- The limit of the lim sup is the infimum of the range of the sequence.
  if limType == "supremum"
  then mustHave "lim sup must exist" $ infimum $ range $ seqDim_ "supremum" seq
  else mustHave "lim inf must exist" $ supremum $ range $ seqDim_ "infimum" seq

limSup :: (Defined set (ExtRD n), KnownNat n)
  => Sequence set (ExtRD n) -> Vector n ExtR
limSup vseq = Vec $ map (limitDim_ "supremum") $ stripe vseq

limInf :: (Defined set (ExtRD n), KnownNat n)
  => Sequence set (ExtRD n) -> Vector n ExtR
limInf vseq = Vec $ map (limitDim_ "infimum") $ stripe vseq

-- Recommended
lim :: (Defined set (ExtRD n), KnownNat n) =>
  Sequence set (ExtRD n) -> Maybe (ExtRD n)
lim vseq = if (limSup vseq) == (limInf vseq)
  then Just (limSup vseq) else Nothing

-------------- Subsequences ------------------

-- There exists mapping (1 -> 4, 2 -> 9, 3 -> 16, etc.)
subseq :: (Defined set a, Eq a) => Sequence set a -> Sequence set a -> Bool
seqa `subseq` seqb = thereExists
  (Everything :: Increasing (Sequence Positive Integer)) $ \map ->
    forAll (Everything :: Positive Integer) $ \n -> seqa ⬅ n == seqb ⬅ map ⬅ n

-- Bolzano-Weierstrass
-- The theorem does not claim any result about unbounded sequences (it could
-- be that they are oscillating) so the result for unbounded is undefined.
-- B-W theorem guarantees the output of this function is never empty
-- for bounded sequences
convergentSubseq :: (KnownNat n, Defined set (RD n))
  => Sequence set (RD n) -> Subset (Sequence set (RD n))
convergentSubseq seq = everything % \s -> s `subseq` seq && (isJust $ lim $ extendFn <. s)

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

approaches :: KnownNat n => ExtRD n -> Subset (Sequence AllOf (RD n))
approaches target = everything % \seq ->
  seq `converges` target &&
  forAll (Everything :: Positive Integer) ( -- Remembber this part!
    \n -> extend (seq ⬅ n) /= target)

-------------- Series / Summation /Union of sequences ------------------

series :: (Eq b, Num b, Defined cod b) => Sequence cod b -> Sequence AllOf b
series seq = mustHave "summation of fine Num terms must succeed" $
  box $ \n -> sum $ map (f seq) [1..n]

-- Sum of a sequence of vectors.
-- Since the output is ExtRD, and the sequence we're limiting is the series
-- (which is always nondecreasing), this will always generate a value
-- (which may be infinite)
sumSeq :: (KnownNat n, Num (ExtRD n), Defined cod (ExtRD n)) =>
  Sequence cod (ExtRD n) -> ExtRD n
sumSeq seq = mustHave "see comment above" $ lim $ series seq

unionSeq :: (Eq (set w), Defined set w, Defined cod (set w))
  => Sequence cod (set w) -> Subset w
unionSeq seq = seq ⬅ 1 ∪ unionSeq (seqTail seq 1)
