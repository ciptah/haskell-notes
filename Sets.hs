-- Set theory formalized in Haskell.
-- Not meant to be fast (or be actually run), it's just to make things formal.
-- Not using Data.Set so we don't have to use Ord types.

module Sets (
  Set(EmptySet, Reals),
  isEmpty,
  member,
  isSubsetOf,
  minus,
  union,
  intersect,
  forAll,
  thereExists,
  unionAll,
  asList
) where

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
