{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}

-- Set theory in Haskell (v2)
-- There are two "primitive" operations:
--   1. Equality with empty set
--   2. Pulling out the sole element of a singleton set.
-- The rest can be defined using these two without any circular definitions.
--
-- Lessons from previous implementation:
--   1. Previous implementation is not great for codomains
--   2. No ability to declare in type what kind of set something is
--
-- To fix these problems we'll attach Symbols to the sets.

module Sets2(
) where

import Data.Maybe (Maybe)

import GHC.TypeLits
import Data.Proxy

-- A (mathematical) set of x.
-- The symbol description is the "codomain". For example, positive reals, etc.
data Set (s :: Symbol) w =
  Everything (Proxy s) |
  forall r. (WellDefined (Set r)) => Subset (w -> Bool) (Set r w) (Proxy s)

-- Shorthand for subset constructor
infixl 1 %
(%) :: (WellDefined (Set s)) => Set s a -> (a -> Bool) -> Set "Filtered" a
set % predicate = Subset predicate set Proxy

class Valid w where
  isValid :: w -> Bool
  isValid _ = True

class WellDefined a where
  exists :: a b -> b -> Bool

instance WellDefined (Set "Unrestricted") where
  exists _ _ = True

instance WellDefined (Set "Filtered") where
  exists (Subset p set _) x = exists set x && p x

-------------- Examples ---------------------

type RealNum = Double

-- Sets of real numbers and their definitions.
type Reals = Set "Unrestricted" RealNum
type PositiveReals = Set "> 0" RealNum

-- Now to make positive reals well defined.
