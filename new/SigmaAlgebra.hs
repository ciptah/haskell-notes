{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SigmaAlgebra (
  SigmaAlgebra(outcomes, events),
  canMeasure, subOf, generate,
  borelRd,

  TimeIndexedSA,
  filtrations, isFiltration
) where

import Data.Maybe
import GHC.TypeLits

import Sets
import Vectors
import Analysis
import Functions

--------------- Definition & Construction --------------

data SigmaAlgebra set w = SigmaAlgebra {
  outcomes :: set w,
  events :: Subset (Subset w)
}

-- Define the validity of all sigma-algebra constructions.
-- The SA must be self-consistent.
instance (Defined set w, Eq w) => Defined AllOf (SigmaAlgebra set w) where
  candidate _ sa = and [
    -- Events must be subsets of the sample set.
    forAll (events sa) $ \ev -> ev ⊆ outcomes sa,
    -- Includes empty set.
    empty ∈ events sa,
    -- Closed under complement.
    forAll (events sa) $ \ev -> (outcomes sa `minus` ev) ∈ events sa,
    -- Closed under countable unions.
    forAll (countableUnions $ events sa) $ \union -> union ∈ events sa]

instance (Eq w, Defined set w) => Eq (SigmaAlgebra set w) where
  -- Events contain the outcome, so we don't need to check eq of the outcomes.
  sa1 == sa2 = events sa1 === events sa2

-- Whether this algebra can understand/measure this event.
canMeasure :: Defined AllOf w => SigmaAlgebra set w -> Subset w -> Bool
sa `canMeasure` event = event ∈ events sa

-- Whether this S-A is included in another. Strict.
subOf :: (Eq w, Defined set w)
  => SigmaAlgebra set w -> SigmaAlgebra set w -> Bool
sa `subOf` sb = sa /= sb && outcomes sa === outcomes sb && events sa ⊆ events sb

-- Generate from a set. Find the unique minimal S-A that contains all events.
-- If samples and seed aren't compatible this might fail to produce a result.
generate :: (Eq w, Defined set w, Defined set1 (Subset w))
  => set w -> set1 (Subset w) -> Maybe (SigmaAlgebra set w)
generate out seed = 
  let candidates = everything % \sa -> outcomes sa === out && seed ⊆ events sa
  in if forAll seed $ \event -> event ⊆ out then
    -- Emphasize that this always succeeds.
    Just $ fromJust $ singleton $ candidates % \sa ->
      (forAll candidates $ \sb -> sa == sb || sa `subOf` sb)
  else Nothing

--------------- The Borel σ-algebra of Real numbers --------

borelRd :: (KnownNat n) => SigmaAlgebra AllOf (RD n)
borelRd = fromJust $ generate everything (everything % open)
  -- Everything #1 is every real. Everything #2 is every subset.
  where open = \set -> forAll set (interior set) -- Open set = all pts are itr

--------------- Filtrations ------------------

-- Filtrations are important for stochastic processes.

type TimeIndexedSA set w = Fn NonNegative R1 AllOf (SigmaAlgebra set w)

type Filtration = Set "Filtration"

instance (Defined set w, Eq w) => Defined Filtration (TimeIndexedSA set w) where
  candidate _ filt =
    forAll time $ \t1 ->
      forAll (time % (t1 <)) $ \t2 ->
        (filt ← t1) `subOf` (filt ← t2)
    where time = Everything :: NonNegative R1

-- Get me all possible filtrations of the outcome set.
filtrations :: (Defined set w, Eq w) => Filtration (TimeIndexedSA set w)
filtrations = Everything

isFiltration :: (Eq w, Defined set w) => TimeIndexedSA set w -> Bool
isFiltration fsa = fsa ∈ filtrations