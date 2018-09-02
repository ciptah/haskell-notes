{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE UndecidableSuperClasses   #-}

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

module Sets
  ( Set(Everything)
  , Defined(candidate)
  , AllOf
  , Subset
  , Zero(..)
  , everything
  , (%)
  , (∈) -- u2208
  , member
  , (∉) -- u2209
  , notMember
  , valid
  , empty
  , intersect
  , minus
  , complement
  , union
  , star
  , unionAll
  , intersectAll
  , thereExists
  , singleton
  , forAll
  , isEmpty
  , isSingleton
  , setEquals
  , (===)
  , (=/=)
  , singletonOf
  , smap
  , cartesian
  , mask
  , isSubsetOf
  , (⊆) -- u2286
  , isDisjoint
  , (∩) -- u2229
  , (∪) -- u222a
  , power
  , countableUnions
  , isPairwiseDisjoint
  , collapse
  , mustHave
  , RealNum
  , Positive
  , Negative
  , NonNegative
  , ZeroOne
  , Increasing
  , NonDecreasing
  , Time
  , Naturals
  )
where

import           Data.Maybe

import           Data.Proxy
import           GHC.TypeLits

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

-- Things with a "Zero" element.
class (Eq x, Num x, Ord x) => Zero x where zero :: x

-- Things that can be turned into a set.
class AsASet set contents where
  asSet :: set -> Subset contents

instance Zero RealNum where zero = 0.0
instance Zero Integer where zero = 0

-- To put a data type in a Set, need to define what "All" means.
everything :: (Defined AllOf w) => AllOf w
everything = Everything

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
-- UNDECIDABLE: instance (Defined (Set z) r) => Defined (Set z) [r] where
instance (Defined AllOf r) => Defined AllOf [r] where
  candidate set xs = and $ map valid xs

instance (Defined AllOf r, Eq r) => Defined [] r where
  candidate list x = x `elem` list

instance (Defined AllOf r, Eq r) => Defined AllOf (Maybe r) where
  candidate _ (Just x) = valid x
  candidate _ Nothing  = True

instance (Defined AllOf a, Defined AllOf b) => Defined AllOf (a, b) where
  candidate _ (a, b) = valid a && valid b

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

intersect :: (Defined set1 w, Defined set2 w) => set1 w -> set2 w -> Subset w
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

intersectAll :: (Defined set a, Foldable t) => t (set a) -> Subset a
intersectAll = foldr intersect (everything % \x -> True)

-------------- Magical Ops ------------------

thereExists :: (Defined set w) => set w -> (w -> Bool) -> Bool
thereExists set predicate = error "***** MAGIC *****"

-- Pulling things out of a singleton set can't be done with just a
-- "there exists" oracle.
singleton :: (Defined set w) => set w -> Maybe w
singleton set = error "***** MAGIC *****"

mustHave :: String -> Maybe w -> w
mustHave justification set = error "***** MAGIC *****"

-------------- Ops that need magic ------------------

forAll :: (Defined set w) => set w -> (w -> Bool) -> Bool
forAll set predicate = not $ thereExists set (not . predicate)

isEmpty :: (Defined set w) => set w -> Bool
isEmpty set = thereExists set $ \any -> True

-- Singleton means there are two things in the set that aren't the same.
isSingleton set = isJust $ singleton set

-- Instance "Eq" doesn't work here because the types are different.
setEquals :: (Defined set1 w, Defined set2 w) => set1 w -> set2 w -> Bool
setEquals set1 set2 = not $ thereExists everything $ \x ->
  (x ∈ set1 && x ∉ set2) || (x ∈ set2 && x ∉ set1)

infix 4 ===
set1 === set2 = set1 `setEquals` set2

infix 4 =/=
set1 =/= set2 = not $ set1 === set2

-- DON'T DO THIS, NON-TERMINATING
-- instance Defined set w => Eq (set w) where
instance Defined AllOf w => Eq (Subset w) where
  s1 == s2 = s1 === s2

-- Construct a singleton set.
singletonOf :: (Eq w, Defined AllOf w) => w -> Subset w
singletonOf x = everything % \y -> y == x

-- smap - Set map, similar to fmap, but only for Eq-able targets.
smap
  :: (Defined set1 a, Defined AllOf b, Eq b) => (a -> b) -> set1 a -> Subset b
smap fn set = everything % \y -> thereExists set $ \x -> fn x == y

-- Cartesian product.
cartesian
  :: (Defined set1 w1, Defined set2 w2) => set1 w1 -> set2 w2 -> Subset (w1, w2)
cartesian setA setB = everything % \(w1, w2) -> w1 ∈ setA && w2 ∈ setB

-------------- Subset operators ---------------------

-- Turns a generic set into a subset, hiding its original type.
mask :: (Defined set w) => set w -> Subset w
mask set = set % \x -> True

-- isEmpty isn't necessary. Just compare with empty
-- The empty set is disjoint with itself, that's intentional [wikipedia].
a `isSubsetOf` b = a === (a ∩ b)
x `isDisjoint` y = x ∩ y === empty
infix 4 ⊆ -- u2286
a ⊆ b = a `isSubsetOf` b

power :: (Defined AllOf w) => Subset w -> Subset (Subset w)
power set = everything % \sub -> sub ⊆ set

-- Given a set of sets X, return the set of sets made by countable unions
-- of elements of X.
countableUnions
  :: (Defined AllOf a, Defined set (Subset a))
  => set (Subset a)
  -> Subset (Subset a)
countableUnions x =
  everything % \y -> thereExists (star x) $ \seq -> unionAll seq == y

-- isPairwiseDisjoint intentionally not from Set (Set a), but from [Set a].
-- This is so the behavior in duplicate sets is defined (will return False)
-- Take care not to include the set in the same indices as pairs
-- This method is computable for list sets.
isPairwiseDisjoint :: Defined AllOf a => [Subset a] -> Bool
isPairwiseDisjoint sets = and $ map disjoint setPairs
 where
  indices    = [0 .. (length sets)]
  indexPairs = [ (x, y) | x <- indices, y <- indices ]
  diffPairs  = filter (\(x, y) -> x /= y) indexPairs
  setPairs   = map (\(x, y) -> (sets !! x, sets !! y)) diffPairs
  disjoint (x, y) = x `isDisjoint` y

collapse
  :: (Defined set (Maybe a), Defined AllOf a) => set (Maybe a) -> Subset a
collapse s = everything % \x -> Just x ∈ s

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
instance Defined ZeroOne RealNum where candidate set x = x >= 0 && x <= 1

instance Defined AllOf Integer where candidate set x = True
instance Defined ZeroOne Integer where candidate set x = x >= 0 && x <= 1

instance (Defined AllOf x, Zero x) => Defined Positive x where
  candidate _ x = x > zero
instance (Defined AllOf x, Zero x) => Defined Negative x where
  candidate _ x = x > zero
instance (Defined AllOf x, Zero x) => Defined NonNegative x where
  candidate _ x = x >= zero

type Time = NonNegative RealNum
type Naturals = Positive Integer

instance Defined Increasing [RealNum] where
  candidate _ []           = True
  candidate _ (x:[])       = True
  candidate set (y:(x:xs)) = y < x && candidate set (x:xs)

instance Defined NonDecreasing [RealNum] where
  candidate _ []           = True
  candidate _ (x:[])       = True
  candidate set (y:(x:xs)) = y <= x && candidate set (x:xs)
