-- Set theory formalized in Haskell.

module Sets (
  Set(EmptySet, Reals),
  Collection,
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
  isDisjoint,
  isAllDisjoint,
  countableProduct,
  countableUnions
) where

-- Not "strictly" true but close enough for this discussion.
type Collection = Set

-- Mathematical "For all"
forAll :: (Foldable t) => t a -> (a -> Bool) -> Bool
forAll s pred = foldr (\x z -> (pred x) && z) True s

-- Mathematical "There Exists"
thereExists :: (Foldable t) => t a -> (a -> Bool) -> Bool
thereExists s pred = foldr (\x z -> (pred x) || z) False s

-- A (mathematical) set of x. Some examples.
data Set w = EmptySet | Reals deriving (Eq, Show)

instance Foldable Set where
  foldr f z EmptySet = z
  foldr f z s = error "Not implemented"

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

minus :: Set a -> Set a -> Set a
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

-- Disjoint, aka no intersection.
isDisjoint :: Set a -> Set a -> Bool
isDisjoint x y = x `intersect` y == EmptySet

-- Are all the sets in the given list disjoint with one another?
isAllDisjoint :: [Set a] -> Bool
isAllDisjoint sets = forAll cartesianProduct $ \(x, y) -> x `isDisjoint` y
    where cartesianProduct = [ (x, y) | x <- sets, y <- sets ]

-- Get all possible N-fold cartesian products
countableProduct :: Set a -> [[a]]
countableProduct set = result
    where result = [ add:cur | cur <- []:result, add <- (asList set) ]

-- Given a set of sets, return a sequence of sets made of the countable
-- unions of the elements in the set.
countableUnions :: Collection (Set a) -> [Set a]
countableUnions sets = map unionAll $ countableProduct sets
