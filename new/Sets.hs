{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}

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
  Defined(candidate),
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
  power, countableUnions, isPairwiseDisjoint,

  RealNum,
  Positive,
  Negative,
  NonNegative,
  ZeroOne,
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
-- within the set. The special "AllOf x" construction has to be defined first,
-- then any custom singleton subset can be defined.
class (Defined AllOf contents) => Defined set contents where
  -- Means this element meets some necessary requirement ot be part of the set.
  -- However, the element still has to satisfy (AllOf contents) before it can
  -- be said to be part of the set.
  candidate :: set contents -> contents -> Bool

-- To put a data type in a Set, need to define what "All" means.
everything :: (Defined AllOf w) => AllOf w
everything = Everything -- DO NOT CREATE Everything ANYWHERE ELSE

valid :: (Defined AllOf w) => w -> Bool
valid x = candidate everything x -- Prevent recursive definition

-- Shorthand for subset constructor
infixl 1 %
(%) :: (Defined set a) => set a -> (a -> Bool) -> Subset a
set % predicate = Subset predicate set

--------------------------------------------

instance (Defined AllOf r) => Defined Subset r where
  candidate (Subset p set) x = candidate set x && p x

-- If we can define what "all of x" is, then we can define all of its subsets.
instance (Defined AllOf r) => Defined AllOf (Subset r) where
  candidate _ subset = subset ⊆ everything -- is this always True?

-- If some set of r is defined, then the same kind of set on the list of r
-- is also defined. This means from (Positive Integer) we can get definition
-- of (Positive [Intenger]), (Positive [[Integer]]), ...
instance (Defined (Set z) r) => Defined (Set z) [r] where
  candidate set xs = and $ map valid xs

instance (Defined AllOf x0, Defined AllOf x1) => Defined AllOf (x0, x1) where
  candidate set (x0, x1) = valid x0 && valid x1

instance (Defined AllOf x0, Defined AllOf x1, Defined AllOf x2)
    => Defined AllOf (x0, x1, x2) where
  candidate set (x0, x1, x2) = valid x0 && valid x1 && valid x2

instance (
    Defined AllOf x0,
    Defined AllOf x1,
    Defined AllOf x2,
    Defined AllOf x3
    ) => Defined AllOf (x0, x1, x2, x3) where
  candidate set (x0, x1, x2, x3) = valid x0 && valid x1 && valid x2 && valid x3

instance (
    Defined AllOf x0,
    Defined AllOf x1,
    Defined AllOf x2,
    Defined AllOf x3,
    Defined AllOf x4
    ) => Defined AllOf (x0, x1, x2, x3, x4) where
  candidate set (x0, x1, x2, x3, x4) =
    valid x0 && valid x1 && valid x2 && valid x3 && valid x4

instance (Defined AllOf r, Eq r) => Defined [] r where
  candidate list x = x `elem` list

-------------- Membership ------------------

infix 4 ∈  -- Unicode hex 2208
(∈) :: (Defined set contents) => contents -> set contents -> Bool
x ∈ set = valid x && candidate set x

member :: (Defined set contents) => contents -> set contents -> Bool
member = (∈)

notMember :: (Defined set contents) => contents -> set contents -> Bool
notMember x set = not (x ∈ set)

infix 4 ∉  -- Unicode hex 2209
(∉) :: (Defined set contents) => contents -> set contents -> Bool
(∉) = notMember

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
star :: (Defined set w) => set w -> Subset [w]
star set = everything % \xs -> and $ map (set `candidate`) xs

unionAll :: (Defined set a, Foldable t) => t (set a) -> Subset a
unionAll = foldr union empty

intersectAll :: (Defined set a, Foldable t) =>
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
setEquals :: (Defined set1 w, Defined set2 w) =>
  set1 w -> set2 w -> Bool
setEquals set1 set2 = not $ thereExists everything $ \x ->
  (x ∈ set1 && x ∉ set2) || (x ∈ set2 && x ∉ set1)

infix 4 ===
set1 === set2 = set1 `setEquals` set2

infix 4 =/=
set1 =/= set2 = not $ set1 === set2

instance Defined AllOf w => Eq (Subset w) where
  s1 == s2 = s1 === s2

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

-------------- Subset operators ---------------------

-- Turns a generic set into a subset, hiding its original type.
mask :: (Defined set w) => set w -> Subset w
mask set = set % \x -> True

-- isEmpty isn't necessary. Just compare with empty
-- The empty set is disjoint with itself [wikipedia].
a `isSubsetOf` b = a === (a ∩ b)
x `isDisjoint` y = x ∩ y === empty
infix 4 ⊆ -- u2286
a ⊆ b = a `isSubsetOf` b

power :: (Defined AllOf w) => Subset w -> Subset (Subset w)
power set = everything % \sub -> sub ⊆ set

-- Given a set of sets X, return the set of sets made by countable unions
-- of elements of X.
countableUnions :: (Defined AllOf a, Defined set (Subset a))
  => set (Subset a) -> Subset (Subset a)
countableUnions x =
    everything % \y -> thereExists (star x) $ \seq -> unionAll seq == y

-- isPairwiseDisjoint intentionally not from Set (Set a), but from [Set a].
-- This is so the behavior in duplicate sets is defined (will return False)
-- Take care not to include the set in the same indices as pairs
-- This method is computable for list sets.
isPairwiseDisjoint :: Defined AllOf a => [Subset a] -> Bool
isPairwiseDisjoint sets = and $ map disjoint setPairs
  where indices = [0..(length sets)]
        indexPairs = [(x, y) | x <- indices, y <- indices]
        diffPairs = filter (\(x, y) -> x /= y) indexPairs
        setPairs = map (\(x, y) -> (sets!!x, sets!!y)) diffPairs
        disjoint (x, y) = x `isDisjoint` y

-------------- Examples ---------------------

type RealNum = Double
type Positive = Set "> 0"
type Negative = Set "< 0"
type NonNegative = Set ">= 0"
type ZeroOne = Set "[0, 1]"

type Increasing = Set "Increasing"
type NonDecreasing = Set "NonDecreasing"

instance Defined AllOf Bool where candidate set x = True

instance Defined AllOf RealNum where candidate set x = True
instance Defined Positive RealNum where candidate set x = x > 0
instance Defined Negative RealNum where candidate set x = x < 0
instance Defined NonNegative RealNum where candidate set x = x >= 0
instance Defined ZeroOne RealNum where candidate set x = x >= 0 && x <= 1

instance Defined AllOf Integer where candidate set x = True
instance Defined Positive Integer where candidate set x = x > 0
instance Defined Negative Integer where candidate set x = x < 0
instance Defined NonNegative Integer where candidate set x = x >= 0
instance Defined ZeroOne Integer where candidate set x = x >= 0 && x <= 1
