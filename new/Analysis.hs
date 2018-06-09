{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}

-- https://www.math.ucdavis.edu/~hunter/intro_analysis_pdf/intro_analysis.pdf
module Analysis(
  bounds, upperBounds, lowerBounds,
  bounded, upperBounded, lowerBounded,
  supremum, infimum,
  supremumFn, infimumFn, mappers,
  equalCardinality, finite, countable,
  interior, neighborhood, isolated, boundary, accumulation
) where

import Sets
import Functions
import Vectors
import GHC.TypeLits

data Bound x = UpperBound x | LowerBound x
isUpperBound (UpperBound _) = True
isUpperBound (LowerBound _) = False
isLowerBound (LowerBound _) = True
isLowerBound (UpperBound _) = False
valueOf (UpperBound x) = x
valueOf (LowerBound x) = x

instance (Defined AllOf x) => Defined AllOf (Bound x) where
  candidate _ (UpperBound b) = valid b
  candidate _ (LowerBound b) = valid b

-------------- Bounds of sets ------------------

-- Find all bounds and put them into one set.
-- From all "claimants", filter to the ones that actually is a bound
bounds :: (Defined set x, Ord x) => set x -> Subset (Bound x)
bounds set = everything % \r -> forAll set $ \x -> r `bounds` x
  where (UpperBound r) `bounds` x = r >= x
        (LowerBound r) `bounds` x = r <= x

-- Subset of Everything that are upper/lower bounds of a set
upperBounds set = smap valueOf (bounds set % isUpperBound)
lowerBounds set = smap valueOf (bounds set % isLowerBound)

bounded :: (Defined set x, Ord x) => set x -> Bool
upperBounded set = upperBounds set /= empty
lowerBounded set = lowerBounds set /= empty
bounded set = upperBounded set && lowerBounded set

-- Sup: Get the one value from all upper bounds that's less than all other
-- upper bounds. May not exist depending on the set.
supremum :: (Defined set x, Ord x) => set x -> Maybe x
supremum set = singleton $ b % \x -> forAll b $ \y -> x <= y -- least upper bound
  where b = upperBounds set

infimum :: (Defined set x, Ord x) => set x -> Maybe x
infimum set = singleton $ b % \x -> forAll b $ \y -> x >= y -- most lower bound
  where b = lowerBounds set

-------------- Bounds/maps of functions ------------------

supremumFn :: (Defined dom x, Defined cod RealNum)
  => Fn dom x cod RealNum -> Subset x -> Maybe RealNum
supremumFn fn set = supremum $ smap (f fn) set

infimumFn :: (Defined dom x, Defined cod RealNum)
  => Fn dom x cod RealNum -> Subset x -> Maybe RealNum
infimumFn fn set = infimum $ smap (f fn) set

-- Find all (bijective mappings from one set to another)
-- By definition the existence of this bijective mapping means the sets
-- must have same cardinality.
mappers :: (Eq a, Eq b, Defined set1 a, Defined set2 b)
  => set1 a -> set2 b -> Subset (Fn set1 a set2 b)
mappers x y = everything % \boxed -> bijective boxed

-------------- Cardinality & Finiteness ------------------

equalCardinality :: (Eq a, Eq b, Defined set1 a, Defined set2 b)
  => set1 a -> set2 b -> Bool
equalCardinality x y = mappers x y =/= empty

-- All sets of the form {1, ... n} for some n ∈ naturals
-- Equivalently, meaning the set is bounded by 0 and n for some n
-- AND, that it is contiguous i.e. including all the numbers
type Index = Set "Index"
instance Defined Index [Integer] where
  candidate _ list = thereExists (Everything :: NonNegative Integer) $
    \bigN -> list == [1..bigN]

finite :: (Defined set a, Eq a) => set a -> Bool
finite x = x === empty || (
  thereExists (Everything :: Index [Integer]) $
    \ix -> x `equalCardinality` ix)

countable x = finite x || x `equalCardinality` (Everything :: Positive Integer)

-------------- Classification of points in Rd ------------------
-- https://en.wikipedia.org/wiki/Open_set
-- https://en.wikipedia.org/wiki/Neighbourhood_(mathematics)

-- Interior point if there exists open ball (which implies neighborhood)
-- The wikipedia page uses strict contains, but this is equivalent, because
-- we can just halve the "proofing" delta to get a proper subset.
interior :: (Defined set (RD n), KnownNat n) => set (RD n) -> RD n -> Bool
interior set x = thereExists (Everything :: Positive RealNum) $
  \d -> OpenBall x d ⊆ set

-- Neighborhood if it contains an open ball of the point.
-- The focus here is on the point, instead of the set.
neighborhood :: (Defined set (RD n), KnownNat n) => RD n -> set (RD n) -> Bool
neighborhood = flip interior

-- an isolated point of A if x ∈ A and there exists δ > 0 such that x is the
-- only point in A that belongs to the interval (x − δ, x + δ)
isolated :: (Defined set (RD n), KnownNat n) => set (RD n) -> RD n -> Bool
isolated set x = thereExists (Everything :: Positive RealNum) $
  \d -> set ∩ OpenBall x d == singletonOf x -- x ∈ set is implied

using :: String -> Bool
using = error "Blah"

-- a boundary point of A if for every δ > 0 the interval (x − δ, x + δ)
-- contains points in A and points not in A
boundary :: (Defined set (RD n), KnownNat n) => set (RD n) -> RD n -> Bool
boundary set x | using "Self definition" =
  forAll (Everything :: Positive RealNum) $
    \d -> let ball = OpenBall x d in
      ball ∩ set =/= empty && ball ∩ (complement set) =/= empty
-- Points that are neither the interior of the set or complement of set.
-- This makes it real clear that the boundary is shared between the set
-- and complement of the set.
boundary set x | using "Negation" =
  (not $ interior (set ∪ singletonOf x) x) &&
  (not $ interior (complement set ∪ singletonOf x) x)

-- an accumulation point of A if for every δ > 0 the interval (x−δ, x+δ)
-- contains a point in A that is distinct from x
-- Accumulation point is like the reverse of isolated (can't be separated),
-- but it may not even belong to the set.
accumulation :: (Defined set (RD n), KnownNat n) => set (RD n) -> RD n -> Bool
accumulation set x = not $ isolated (set ∪ singletonOf x) x
