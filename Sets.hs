{-# LANGUAGE ExistentialQuantification #-}
-- Set theory formalized in Haskell.

module Sets (
  Set(EmptySet, Singleton, AllInType),
  Collection,
  RealNum,
  reals,
  r1, r2,
  integers,
  isEmpty,
  member,
  isSubsetOf,
  minus,
  union,
  intersect,
  forAll,
  thereExists,
  unionAll,
  asList,
  fromList,
  isDisjoint,
  isAllDisjoint,
  star,
  countableUnions,
  singleton,
  (%)
) where

import Data.Maybe (Maybe)

-- Not "strictly" true but close enough for this discussion.
type Collection = Set
type RealNum = Double

-- Mathematical "For all"
forAll :: (Foldable t) => t a -> (a -> Bool) -> Bool
forAll s pred = foldr (\x z -> (pred x) && z) True s

-- Mathematical "There Exists"
thereExists :: (Foldable t) => t a -> (a -> Bool) -> Bool
thereExists s pred = foldr (\x z -> (pred x) || z) False s

-- A (mathematical) set of x. Some examples.
data Set w = EmptySet
    | Singleton w
    | AllInType -- Includes everything defined by the type.
    | forall w. (Ord w) => Interval w w

reals = AllInType :: Set RealNum
r1 = reals
integers = AllInType :: Set Integer
r2 = AllInType :: Set (RealNum, RealNum)

instance Show (Set a) where
  show EmptySet = "{}"
  show x = error "Not Implemented"

instance Eq (Set a) where
  (==) EmptySet EmptySet = True
  (==) x y = error "Not Implemented"

instance Foldable Set where
  foldr f z EmptySet = z
  foldr f z s = error "Not implemented"

instance Functor Set where
  fmap fn EmptySet = EmptySet
  fmap fn set = error "Not implemented"

-- Declare all the common set operations.

isEmpty :: Set a -> Bool
isEmpty EmptySet = True
isEmpty _ = False

member :: (Eq a) => a -> Set a -> Bool
member _ set 
    | set == EmptySet = False
    | otherwise = error "Not implemented"

isSubsetOf :: Set a -> Set a -> Bool
isSubsetOf EmptySet _ = True
isSubsetOf _ _ = error "Not implemented"

minus :: (Eq a) => Set a -> Set a -> Set a
minus EmptySet _ = EmptySet
minus x EmptySet = x
minus x y | x == y = EmptySet
minus _ _ = error "Not implemented"

union :: Set a -> Set a -> Set a
union = error "Not implemented"

intersect :: Set a -> Set a -> Set a
intersect = error "Not implemented"

unionAll :: [Set a] -> Set a
unionAll sets = foldr (union) EmptySet sets

asList :: Set a -> [a]
asList EmptySet = []
asList _ = error "Not implemented"

fromList :: [a] -> Set a
fromList [] = EmptySet
fromList _ = error "Not implemented"

-- Disjoint, aka no intersection.
isDisjoint :: (Eq a) => Set a -> Set a -> Bool
isDisjoint x y = x `intersect` y == EmptySet

-- Are all the sets in the given list disjoint with one another?
isAllDisjoint :: (Eq a) => [Set a] -> Bool
isAllDisjoint sets = forAll cartesianProduct $ \(x, y) -> x `isDisjoint` y
    where cartesianProduct = [ (x, y) | x <- sets, y <- sets ]

-- From a set S = {a, b, c, ...}
-- Build a set S* = {0, a, b, c, ..., aa, ab, ac, ..., }
-- Also known as a Kleene star.
-- This is intentionally a list, so aaba /= aba /= baaa
star :: Set a -> Set [a]
star set = fromList result
    where result = [ add:cur | cur <- []:result, add <- (asList set) ]

-- Given a set of sets, return a sequence of sets made of the countable
-- unions of the elements in the set.
countableUnions :: Collection (Set a) -> Set (Set a)
countableUnions sets = fmap unionAll $ star sets

-- Unpack: If singleton, output inner value. Otherwise, None.
singleton :: Set a -> Maybe a
singleton (Singleton x) = Just x
singleton _ = Nothing

-- Shorthand for filtration
infixl 1 %
(%) :: Set a -> (a -> Bool) -> Set a
set % condition = fromList $ filter condition $ asList set
