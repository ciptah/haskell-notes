{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

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

module Sets(
  Defined(contains),
  AllOf,
  SomeSet,
  everything,
  (%),
) where

import Data.Maybe (Maybe, isJust)

import GHC.TypeLits
import Data.Proxy

-- A (mathematical) set of x.
-- The symbol description is the "codomain". For example, positive reals, etc.
data Set (s :: Symbol) w =
  Everything |
  forall set. (Defined set w) => Subset (w -> Bool) (set w)

-- Sets that are "Defined" means one can test whether an element is included
-- within the set.
class Defined set contents where
  contains :: set contents -> contents -> Bool

type AllOf = Set "All"
type SomeSet = Set "%"

-- To put a data type in a Set, need to define what "All" means.
everything_ :: Set "All" w
everything_ = Everything -- DO NOT CREATE Everything ANYWHERE ELSE

-- Get the set encoded as type as a set.
everything :: (Defined (Set "All") w) => Set "%" w
everything = everything_ % (contains everything_)

-- Shorthand for subset constructor
infixl 1 %
(%) :: (Defined set a) => set a -> (a -> Bool) -> SomeSet a
set % predicate = Subset predicate set

--------------------------------------------

instance Defined SomeSet r where
  contains (Subset p set) x = contains set x && p x
  contains Everything _ = error "Invalid use of Everything"

-- List of sets are OK.
instance (Defined AllOf r) => Defined AllOf [r] where
  contains set xs = and $ map (contains everything) xs

instance (Eq r) => Defined [] r where
  contains list x = x `elem` list

-------------- Membership ------------------

infix 4 ∈  -- Unicode hex 2208
(∈) :: (Defined set contents) => contents -> set contents -> Bool
(∈) = flip contains

member :: (Defined set contents) => contents -> set contents -> Bool
member = (∈)

notMember :: (Defined set contents) => contents -> set contents -> Bool
notMember x set = not (x ∈ set)

infix 4 ∉  -- Unicode hex 2209
(∉) :: (Defined set contents) => contents -> set contents -> Bool
(∉) = notMember

----------------- Base Ops ---------------------

-- The empty set for the given type.
empty :: (Defined AllOf w) => SomeSet w
empty = everything % \any -> False

intersect :: (Defined set1 w, Defined set2 w)
  => set1 w -> set2 w -> SomeSet w
intersect a b = a % \x -> x ∈ b

minus :: (Defined set1 w, Defined set2 w) => set1 w -> set2 w -> SomeSet w
minus a b = a % \x -> x ∉ b

-- Use of everything (without underscore) means it is using the correct
-- universal set
complement a = everything `minus` a

-- Everything except elements that are not in both sets.
union a b = complement $ intersect (complement a) (complement b)

-- Cartesian product.
-- TODO: move to analysis
cartesian ::
  (Eq w3,
   Defined set1 w1,
   Defined set2 w2,
   Defined AllOf w3) =>
  (w1 -> w2 -> w3) -> set1 w1 -> set2 w2 -> SomeSet w3
cartesian fn setA setB = everything % \w ->
  thereExists setA $ \x -> thereExists setB $ \y -> fn x y == w

-- From a set S = {a, b, c, ...}
-- Build a set S* = {0, a, b, c, ..., aa, ab, ac, ..., }
-- Also known as a Kleene star.
-- This is intentionally a list, so aaba /= aba /= baaa
-- The second constraint is necessary to make "everything" work.
star :: (Defined set w, Defined AllOf w) => set w -> SomeSet [w]
star set = everything % \xs -> and $ map (set `contains`) xs

unionAll ::
  (Defined set a, Defined AllOf a, Foldable t) =>
  t (set a) -> SomeSet a
unionAll = foldr union empty

intersectAll ::
  (Defined set a, Defined AllOf a, Foldable t) =>
  t (set a) -> SomeSet a
intersectAll = foldr intersect everything

-------------- Magical Ops ------------------

thereExists :: (Defined set w) => set w -> (w -> Bool) -> Bool
thereExists set predicate = error "***** MAGIC *****"

-- Pulling things out of a singleton set can't be done with just a
-- "there exists" oracle.
singleton :: (Defined set w) => set w -> Maybe w
singleton set = error "***** MAGIC *****"

-------------- Ops that need magic ------------------

isEmpty :: (Defined set w) => set w -> Bool
isEmpty set = thereExists set $ \any -> True

-- Singleton means there are two things in the set that aren't the same.
isSingleton set = isJust $ singleton set

-- Instance "Eq" doesn't work here because the types are different.
setEquals :: (Defined set1 w, Defined set2 w, Defined AllOf w) =>
  set1 w -> set2 w -> Bool
setEquals set1 set2 = not $ thereExists everything $ \x ->
  (x ∈ set1 && x ∉ set2) || (x ∈ set2 && x ∉ set1)

infix 4 ===
set1 === set2 = set1 `setEquals` set2

infix 4 =/=
set1 =/= set2 = not $ set1 === set2

-- Construct a singleton set.
singletonOf :: (Eq w, Defined AllOf w) => w -> SomeSet w
singletonOf x = everything % \y -> y == x

-- smap - Set map, similar to fmap, but only for Eq-able targets.
smap :: (Defined set1 a, Defined AllOf b, Eq b) =>
  (a -> b) -> set1 a -> SomeSet b
smap fn set = everything % \y -> thereExists set $ \x -> fn x == y

-------------- Examples ---------------------

type RealNum = Double
type Positive = Set "> 0"
type Negative = Set "< 0"
type NonNegative = Set ">= 0"

type Increasing = Set "Increasing"
type NonDecreasing = Set "NonDecreasing"

instance Defined AllOf RealNum where contains set x = True
instance Defined Positive RealNum where contains set x = x > 0
instance Defined Negative RealNum where contains set x = x < 0
instance Defined NonNegative RealNum where contains set x = x >= 0

instance Defined AllOf Integer where contains set x = True
instance Defined Positive Integer where contains set x = x > 0
instance Defined Negative Integer where contains set x = x < 0
instance Defined NonNegative Integer where contains set x = x >= 0
