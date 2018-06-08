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
  Subset,
  everything,
  (%),

  (∈), member, -- u2208
  (∉), notMember, -- u2209
  valid,

  empty, intersect, minus, complement, union, star, unionAll, intersectAll,
  thereExists, singleton, forAll, isEmpty, isSingleton, setEquals, (===), (=/=),
  singletonOf, smap, cartesian,
  isSubsetOf, (⊆), isDisjoint, -- u2286
  (∪), (∩), -- u222a, u2229

  RealNum,
  Positive,
  Negative,
  NonNegative,
  Increasing,
  NonDecreasing
) where

import Data.Maybe (Maybe, isJust)

import GHC.TypeLits
import Data.Proxy

-- Set whose membership is defined by the symbol and content type.
data Set (s :: Symbol) w = Everything

-- All valid items of the given set.
type AllOf = Set "All"

-- Some subset of the given type.
data Subset w = forall set. (Defined set w) => Subset (w -> Bool) (set w)

-- Sets that are "Defined" means one can test whether an element is included
-- within the set.
class Defined set contents where
  contains :: set contents -> contents -> Bool

-- To put a data type in a Set, need to define what "All" means.
everything :: (Defined AllOf w) => AllOf w
everything = Everything -- DO NOT CREATE Everything ANYWHERE ELSE

-- Shorthand for subset constructor
infixl 1 %
(%) :: (Defined set a) => set a -> (a -> Bool) -> Subset a
set % predicate = Subset predicate set

--------------------------------------------

instance Defined Subset r where
  contains (Subset p set) x = contains set x && p x

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

valid :: (Defined AllOf w) => w -> Bool
valid x = x ∈ everything

----------------- Base Ops ---------------------

-- The empty set for the given type.
empty :: (Defined AllOf w) => Subset w
empty = everything % \any -> False

intersect :: (Defined set1 w, Defined set2 w)
  => set1 w -> set2 w -> Subset w
intersect a b = a % \x -> x ∈ b

minus :: (Defined set1 w, Defined set2 w) => set1 w -> set2 w -> Subset w
minus a b = a % \x -> x ∉ b

-- Use of everything (without underscore) means it is using the correct
-- universal set
complement a = everything `minus` a

-- Everything except elements that are not in both sets.
union a b = complement $ intersect (complement a) (complement b)

infixl 6 ∪ -- u222A
infixl 7 ∩ -- u2229
a ∪ b = a `union` b
a ∩ b = a `intersect` b

-- From a set S = {a, b, c, ...}
-- Build a set S* = {0, a, b, c, ..., aa, ab, ac, ..., }
-- Also known as a Kleene star.
-- This is intentionally a list, so aaba /= aba /= baaa
-- The second constraint is necessary to make "everything" work.
star :: (Defined set w, Defined AllOf w) => set w -> Subset [w]
star set = everything % \xs -> and $ map (set `contains`) xs

unionAll ::
  (Defined set a, Defined AllOf a, Foldable t) =>
  t (set a) -> Subset a
unionAll = foldr union empty

intersectAll ::
  (Defined set a, Defined AllOf a, Foldable t) =>
  t (set a) -> Subset a
intersectAll = foldr intersect (everything % \x -> True)

-------------- Magical Ops ------------------

thereExists :: (Defined set w) => set w -> (w -> Bool) -> Bool
thereExists set predicate = error "***** MAGIC *****"

-- Pulling things out of a singleton set can't be done with just a
-- "there exists" oracle.
singleton :: (Defined set w) => set w -> Maybe w
singleton set = error "***** MAGIC *****"

-------------- Ops that need magic ------------------

forAll :: (Defined set w) => set w -> (w -> Bool) -> Bool
forAll set predicate = not $ thereExists set (not . predicate)

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
singletonOf :: (Eq w, Defined AllOf w) => w -> Subset w
singletonOf x = everything % \y -> y == x

-- smap - Set map, similar to fmap, but only for Eq-able targets.
smap :: (Defined set1 a, Defined AllOf b, Eq b) =>
  (a -> b) -> set1 a -> Subset b
smap fn set = everything % \y -> thereExists set $ \x -> fn x == y

-- Cartesian product.
-- TODO: move to analysis
cartesian ::
  (Eq w3,
   Defined set1 w1,
   Defined set2 w2,
   Defined AllOf w3) =>
  (w1 -> w2 -> w3) -> set1 w1 -> set2 w2 -> Subset w3
cartesian fn setA setB = everything % \w ->
  thereExists setA $ \x -> thereExists setB $ \y -> fn x y == w

-------------- Examples ---------------------

-- isEmpty isn't necessary. Just compare with empty
-- The empty set is disjoint with itself [wikipedia].
a `isSubsetOf` b = a === (a ∩ b)
x `isDisjoint` y = x ∩ y === empty
infix 4 ⊆ -- u2286
a ⊆ b = a `isSubsetOf` b

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
