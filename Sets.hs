-- Set theory in Haskell.
-- There are two "primitive" operations:
--   1. Checking existence of an element in the set satisfying a predicate
--   2. Pulling out the sole element of a singleton set.
-- The rest can be defined using these two without any circular definitions.

module Sets (
  Set(Everything, Subset),
  Statement,
  (%),
  Collection,
  RealNum,
  member, notMember, (∈), (∉), -- u2208, u2209
  thereExists', forAll', eval, prove, thereExists, forAll,
  intersect, union, minus, complement, (∪), (∩), -- u222a, u2229
  unionAll, intersectAll,
  cartesian, (⨯), -- u2a2f
  isSubsetOf, (⊆), isDisjoint, -- u2286
  isSingleton, singleton, singletonOf,
  isPairwiseDisjoint, isAllDisjoint,
  star,
  countableUnions,
  smap,
  reals, r1, integers, r2, nonnegatives, naturals, empty
) where

import Data.Maybe (Maybe)

-- A (mathematical) set of x.
--
-- The great thing about this construction is that it's possible to just
-- declare impossibly complicated sets with one line. For example,
--
-- Everything :: Set (Integer -> Real -> Real, Maybe (Real -> [Integer]))
--
-- I don't have to worry about how to make all the elements. It's just there,
-- and then I can filter it as needed.
data Set w = Everything | Subset (w -> Bool) (Set w)

-- A statement about some element with a certain property existing in the set.
data Statement w = Exists (Set w) (w -> Bool) | Not (Statement w)

-- Shorthand for subset constructor
infixl 1 %
(%) :: Set a -> (a -> Bool) -> Set a
set % predicate = Subset predicate set

-- Not "completely" true but it's OK for now.
type Collection = Set
type RealNum = Double



-- The way we construct sets means membership can be computed exactly.
member :: a -> Set a -> Bool
member _ Everything = True
member x (Subset predicate set) = x `member` set && predicate x
notMember x set = not $ x `member` set
-- Fixity is above &&, || etc.
infix 4 ∈  -- Unicode hex 2208
(∈) = member
infix 4 ∉  -- Unicode hex 2209
(∉) = notMember



-- Quantified statements.
-- The functions with backticks construct a statement, the ones without
-- attempts to evaluate a statement.

thereExists' :: Set a -> (a -> Bool) -> Statement a
thereExists' inSet predicate = Exists inSet predicate
forAll' inSet predicate = neg $ Exists inSet (not . predicate)

neg :: Statement a -> Statement a
neg (Exists x y) = Not $ Exists x y
neg (Not x) = x

eval :: Statement a -> Bool
eval (Not x) = not $ eval x
eval (Exists inSet predicate) = error "** Magic **"

-- Exists statements can be proven, if you supply a satisfying element
prove (Exists inSet predicate) proof =
    if proof ∈ inSet && predicate proof then "QED" else error "D'oh!!"

thereExists inSet predicate = eval $ thereExists' inSet predicate
forAll inSet predicate = eval $ forAll' inSet predicate



-- Set operations
intersect a b = a % \x -> x ∈ b
union a b = Everything % \x -> x ∈ a && x ∈ b
minus a b = a % \x -> x ∉ b
complement a = Everything `minus` a
infixl 6 ∪ -- u222A
infixl 7 ∩ -- u2229
(∪) = union
(∩) = intersect

unionAll :: (Foldable t) => t (Set a) -> Set a
unionAll = foldr (∪) empty -- Currying
intersectAll :: (Foldable t) => t (Set a) -> Set a
intersectAll = foldr (∩) Everything

-- Equality using Axiom of extensionality from ZFC
-- Because we use forAll in the definition of Eq, redefining thereExists
--   as (set % condition != empty) will cause a circular definition.
-- We have to make either "there exists" or "Eq" an undefinable primitive.
instance Eq (Set a) where
  x == y = forAll Everything $ \z -> (z ∈ x && z ∈ y) || (z ∉ x && z ∉ y)

-- Cartesian product.
cartesian :: Set a -> Set b -> Set (a, b)
cartesian setA setB = Everything % \(x, y) -> x ∈ setA && y ∈ setB
(⨯) = cartesian

-- Singleton means there are two things in the set that aren't the same.
isSingleton :: (Eq a) => Set a -> Bool
isSingleton set =
  set /= empty && (not $ thereExists (cartesian set set) $ \(x, y) -> x /= y)

-- Pulling things out of a singleton set can't be done with just a
-- "there exists" oracle.
singleton :: (Eq a) => Set a -> Maybe a
singleton set | set == empty = Nothing
              | isSingleton set = error "** Magic **"
              | otherwise = Nothing

-- isEmpty isn't necessary. Just compare with empty
-- The empty set is disjoint with itself [wikipedia].
a `isSubsetOf` b = a == (a ∩ b)
x `isDisjoint` y = x ∩ y == empty
infix 4 ⊆ -- u2286
(⊆) = isSubsetOf

-- isPairwiseDisjoint intentionally not from Set (Set a), but from [Set a].
-- This is so the behavior in duplicate sets is defined (will return False)
-- Take care not to include the set in the same indices as pairs
isPairwiseDisjoint :: [Set a] -> Bool
isPairwiseDisjoint sets = and $ map disjoint setPairs
  where indices = [0..(length sets)]
        indexPairs = [(x, y) | x <- indices, y <- indices]
        diffPairs = filter (\(x, y) -> x /= y) indexPairs
        setPairs = map (\(x, y) -> (sets!!x, sets!!y)) diffPairs
        disjoint (x, y) = x `isDisjoint` y
isAllDisjoint = isPairwiseDisjoint

-- From a set S = {a, b, c, ...}
-- Build a set S* = {0, a, b, c, ..., aa, ab, ac, ..., }
-- Also known as a Kleene star.
-- This is intentionally a list, so aaba /= aba /= baaa
star :: Set a -> Set [a]
star set = Everything % \xs -> and $ map (flip member set) xs

-- Given a set of sets X, return the set of sets made by countable unions
-- of elements of X.
countableUnions :: Set (Set a) -> Set (Set a)
countableUnions x =
    Everything % \y -> thereExists (star x) $ \seq -> unionAll seq == y

-- Throw out everything that isn't x.
singletonOf :: (Eq a) => a -> (Set a)
singletonOf x = Everything % \y -> y == x

-- smap - Set map, similar to fmap, but only for Eq-able contents.
smap :: (Eq b) => (a -> b) -> Set a -> Set b
smap fn set = Everything % \y -> thereExists set $ \x -> fn x == y

-- Some examples.
reals = Everything :: Set RealNum
r1 = reals
integers = Everything :: Set Integer
r2 = Everything :: Set (RealNum, RealNum)
nonnegatives = integers % \i -> i >= 0 -- non-negative integers.
naturals = integers % \i -> i > 0 -- natural numbers
empty = Everything `minus` Everything
