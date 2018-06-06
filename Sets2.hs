{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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

import Data.Maybe (Maybe, isJust)

import GHC.TypeLits
import Data.Proxy

-- A (mathematical) set of x.
-- The symbol description is the "codomain". For example, positive reals, etc.
data Set (s :: Symbol) w =
  Everything |
  forall src. (Defined (Set src) w) => Subset (w -> Bool) (Set src w)

everything_ :: Set "All" w
everything_ = Everything -- DO NOT CREATE Everything ANYWHERE ELSE

everything :: (Defined (Set "All") w) => Set "%" w
everything = everything_ % (contains everything_)

-- Shorthand for subset constructor
infixl 1 %
(%) :: (Defined (Set s) a) => Set s a -> (a -> Bool) -> Set "%" a
set % predicate = Subset predicate set

--------------------------------------------

-- Sets that are "Defined" means one can test whether an element is included
-- within the set.
class Defined set contents where
  contains :: set contents -> contents -> Bool

instance Defined (Set "%") r where
  contains (Subset p set) x = contains set x && p x
  contains Everything _ = error "Invalid use of Everything"

-- List of sets are OK.
instance (Defined (Set "All") r) => Defined (Set "All") [r] where
  contains set xs = and $ map (contains everything) xs

-------------- Membership ------------------

infix 4 ∈  -- Unicode hex 2208
(∈) :: (Defined a b) => b -> a b -> Bool
(∈) = flip contains

member :: (Defined a b) => b -> a b -> Bool
member = (∈)

notMember :: (Defined a b) => b -> a b -> Bool
notMember x set = not (x ∈ set)

infix 4 ∉  -- Unicode hex 2209
(∉) :: (Defined a b) => b -> a b -> Bool
(∉) = notMember

-------------- Magical Ops ------------------

thereExists :: (Defined (Set s) w) => Set s w -> (w -> Bool) -> Bool
thereExists set predicate = error "***** MAGIC *****"

-- Pulling things out of a singleton set can't be done with just a
-- "there exists" oracle.
singleton :: Set s a -> Maybe a
singleton set = error "***** MAGIC *****"

-------------- Functions ------------------

isEmpty :: (Defined (Set s) w) => Set s w -> Bool
isEmpty set = thereExists set $ \any -> True

empty :: (Defined (Set "All") w) => Set "%" w
empty = everything % \any -> False

intersect :: (Defined (Set s) w, Defined (Set r) w)
  => Set s w -> Set r w -> Set "%" w
intersect a b = a % \x -> x ∈ b

minus :: (Defined (Set s) w, Defined (Set r) w)
  => Set s w -> Set r w -> Set "%" w
minus a b = a % \x -> x ∉ b

complement a = everything `minus` a

-- Everything except elements that are not in both sets.
union a b = complement $ intersect (complement a) (complement b)

-- Cartesian product.
-- TODO: move to analysis
cartesian ::
  (Eq w3,
   Defined (Set s) w1,
   Defined (Set r) w2,
   Defined (Set "All") w3) =>
  (w1 -> w2 -> w3) -> Set s w1 -> Set r w2 -> Set "%" w3
cartesian fn setA setB = everything % \w ->
  thereExists setA $ \x -> thereExists setB $ \y -> fn x y == w

-- Singleton means there are two things in the set that aren't the same.
isSingleton set = isJust $ singleton set

-- From a set S = {a, b, c, ...}
-- Build a set S* = {0, a, b, c, ..., aa, ab, ac, ..., }
-- Also known as a Kleene star.
-- This is intentionally a list, so aaba /= aba /= baaa
-- The second constraint is necessary to make "everything" work.
star :: (Defined (Set s) w,
         Defined (Set "All") w) => Set s w -> Set "%" [w]
star set = everything % \xs -> and $ map (set `contains`) xs

-- Instance "Eq" doesn't work here because the types are different.
setEquals ::
  (Defined (Set s) w, Defined (Set r) w, Defined (Set "All") w) =>
  Set s w -> Set r w -> Bool
setEquals set1 set2 = not $ thereExists everything $ \x ->
  (x ∈ set1 && x ∉ set2) || (x ∈ set2 && x ∉ set1)

infix 4 ===
(===) ::
  (Defined (Set s) w, Defined (Set r) w, Defined (Set "All") w) =>
  Set s w -> Set r w -> Bool
set1 === set2 = set1 `setEquals` set2

infix 4 =/=
(=/=) ::
  (Defined (Set s) w, Defined (Set r) w, Defined (Set "All") w) =>
  Set s w -> Set r w -> Bool
set1 =/= set2 = not $ set1 === set2

unionAll ::
  (Defined (Set s) a, Defined (Set "All") a, Foldable t) =>
  t (Set s a) -> Set "%" a
unionAll = foldr union empty

intersectAll ::
  (Defined (Set s) a, Defined (Set "All") a, Foldable t) =>
  t (Set s a) -> Set "%" a
-- Fold doesn't understand hetero types like Sets
-- Which makes this necessary
intersectAll = foldr intersect (everything % \x -> True)

-------------- Examples ---------------------

type RealNum = Double

type AllOf w = Set "All" w

instance Defined (Set "All") RealNum where
  contains set x = True
instance Defined (Set "> 0") RealNum where
  contains set x = x > 0
instance Defined (Set "< 0") RealNum where
  contains set x = x < 0
instance Defined (Set "All") Integer where
  contains set x = True
instance Defined (Set "> 0") Integer where
  contains set x = x > 0
instance Defined (Set "< 0") Integer where
  contains set x = x < 0

-- Sets of real numbers and their definitions.
type Reals = AllOf RealNum
type PositiveReals = Set "> 0" RealNum
type NegativeReals = Set "< 0" RealNum
type Integers = AllOf Integer
type Naturals = Set "> 0" Integer
