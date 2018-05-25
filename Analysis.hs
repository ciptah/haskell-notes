-- https://www.math.ucdavis.edu/~hunter/intro_analysis_pdf/intro_analysis.pdf

module Analysis (
  Boxed(Box),
  Bound,
  halts,
  naked,
  codomain,
  compile,
  preimage, preimageOf,
  domain,
  image, range,
  onto, one2one, bijective,
  isUpperBound, isLowerBound, valueOf,
  bounds, upperBounds, lowerBounds,
  bounded,
  supremum,
  infimum
) where

import Sets

-- Whether the given function halts given the input. This is of course
-- undecidable in the general case.
halts :: (a -> b) -> a -> Bool
halts fn input = error "Turing is mad at you!"

-- We have to remember the codomain of a function because having only
-- Everything as codomain is too restrictive.
-- For example, "Everything" might be Integers but I want 
-- the codomain to be even numbers.

-- We lose the easy currying but we can get it later using tuples.
-- We pair a function with its codomain. By definition if the "natural range"
-- of the function is bigger than the given codomain, it gets truncated.

-- Put a function inside this box to perform "formal analysis"
data Boxed a b = Box {
  naked :: a -> b,
  codomain :: Set b
}

-- "Weld" a box into the function, making it part of the definition.
-- This means the function will blow up if it will return something outside the
-- codomain, making the result "undefined".
compile :: Boxed a b -> a -> b
compile (Box fn codomain) = out
  where out x | fn x ∈ codomain = fn x
              | otherwise = error "Truncated!"

-- Find the preimage of a target set wrt the function.
preimage :: (a -> b) -> Set b -> Set a
preimage fn target = Everything % \x -> fn x `member` target

-- Same of above but only for a single function.
preimageOf :: (Eq b) => (a -> b) -> b -> Set a
preimageOf fn target = preimage fn $ singletonOf target

-- Domain, Codomain, Function, Range
-- Domain is where the function is defined, i.e. halts.
-- For the preimage of the boxed function with a target set, just take the
-- preimage of the intersection between the target and the codomain of the box.
domain :: Boxed a b -> Set a
domain (Box f codomain) = preimage f codomain

-- Image can be thought of as an fmap of a function on a set.
-- The reason a Set isn't a functor is because we need (Eq b) to make this work.
image :: (Eq b) => Boxed a b -> Set b
image boxed = smap (compile boxed) Everything
-- domain is unnecessary because it's defined from the function and codomain
-- which is already compiled into one function. The compiled fn will throw
-- error whenever it's fed something outside the domain.
-- Alternative: codomain % \y -> thereExists (domain b) $ \x -> (fn x) == y
range :: (Eq b) => Boxed a b -> Set b
range = image

onto :: (Eq b) => Boxed a b -> Bool
onto boxed = range boxed == codomain boxed

-- x1, x2 ∈ X and x1 /= x2 implies that f(x1) /= f(x2).
-- forAll (domain ⨯ domain) $ \(x1 x2) -> if x1 /= x2 then f x1 /= f x2 e. F.
one2one :: (Eq a, Eq b) => Boxed a b -> Bool
one2one boxed = -- Alternative way of saying it.
  forAll (codomain boxed) $ \y -> isSingleton $ preimageOf (compile boxed) y

bijective boxed = one2one boxed && onto boxed

-- We're not going to expose these constructors.
data Bound x = UpperBound x | LowerBound x
isUpperBound (UpperBound _) = True
isUpperBound (LowerBound _) = False
isLowerBound (LowerBound _) = True
isLowerBound (UpperBound _) = False
valueOf (UpperBound x) = x
valueOf (LowerBound x) = x

-- Find all bounds and put them into one set.
-- From all "claimants", filter to the ones that actually is a bound
bounds :: (Ord x) => Set x -> Set (Bound x)
bounds set = Everything % \r -> forAll set $ \x -> r `bounds` x
  where (UpperBound r) `bounds` x = r >= x
        (LowerBound r) `bounds` x = r <= x

upperBounds set = smap valueOf (bounds set % isUpperBound)
lowerBounds set = smap valueOf (bounds set % isLowerBound)

bounded :: (Ord x) => Set x -> Bool
bounded set = (upperBounds set) /= empty && (lowerBounds set) /= empty

-- Sup: Get the one value from all upper bounds that's less than all other
-- upper bounds. May not exist depending on the set.
supremum :: (Ord x) => Set x -> Maybe x
supremum set = singleton $ b % \x -> forAll b $ \y -> x <= y -- least upper bound
    where b = upperBounds set

infimum :: (Ord x) => Set x -> Maybe x
infimum set = singleton $ b % \x -> forAll b $ \y -> x >= y -- most lower bound
    where b = lowerBounds set

-- Archimedaean property (Theorem 2.18)
archimedaean = forAll r1 $ \x -> thereExists naturals $ \n -> x < fromIntegral n

-- Finiteness and cardinality.
equalCardinality :: (Eq a, Eq b) => Set a -> Set b -> Bool
equalCardinality x y = thereExists (Everything :: Set (Boxed a b)) $ (
  \boxed -> domain boxed == x && range boxed == y && bijective boxed)

-- All sets of the form {0, 1, ... n} for some n ∈ naturals
-- Equivalently, meaning the set is bounded by 0 and n for some n
indexSets :: Set (Set Integer)
indexSets = Everything % \s -> bounded s && 1 ∈ lowerBounds s

isFinite :: (Eq a) => Set a -> Bool
isFinite x =
  x == empty || (thereExists indexSets $ \ix -> x `equalCardinality` ix)

countable x = isFinite x || x `equalCardinality` naturals

