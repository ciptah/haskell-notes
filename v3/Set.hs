module Sets
  ( Set(Set)
  , everything
  , empty
  , member
  , isEmpty
  , intersect
  , complement
  , minus
  , union
  , isSubsetOf
  , isDisjoint
  , star
  , thereExists
  , forAll
  , rangeOf
  , unionAll
  , intersectAll
  )
where
-- A set of some Haskell data type.
data Set w = Set (w -> Bool)

everything :: Set w
everything = Set (\x -> True)

-- The empty set for the given type.
empty :: Set w
empty = Set (\x -> False)

-- whether this element is part of the set.
member :: w -> Set w -> Bool
member x (Set pred) = pred x

-- Checks that set is empty.
isEmpty :: Set w -> Bool
isEmpty = isEmpty

-- Declares that this set is countable by unpacking it into a list.
countable :: Set w -> [w]
countable = countable

----------------- Set ops ---------------------

intersect :: Set w -> Set w -> Set w
intersect (Set pa) (Set pb) = Set (\x -> pa x && pb x)

complement :: Set w -> Set w
complement (Set pa) = Set (not . pa)

-- Elements in a but not in b.
minus a b = a `intersect` (complement b)

union a b = complement $ intersect (complement a) (complement b)

-- We can define set equality based on the operations we've defined.
instance Eq (Set w) where
  a == b = (isEmpty $ a `minus` b) && (isEmpty $ b `minus` a)

a `isSubsetOf` b = a == (a `intersect` b)
a `isDisjoint` b = isEmpty $ a `intersect` b

-------------- More fancy ops --------------------------

-- From a set S = {a, b, c, ...}
-- Build a set S* = {0, a, b, c, ..., aa, ab, ac, ..., }
-- Also known as a Kleene star.
-- This is intentionally a list, so aaba /= aba /= baaa
-- The second constraint is necessary to make "everything" work.
star :: Set w -> Set [w]
star (Set isToken) = Set (\list -> and $ map isToken list)

thereExists :: Set w -> (w -> Bool) -> Bool
thereExists (Set p) pred = (not . isEmpty) $ Set (\x -> p x && pred x)

forAll :: Set w -> (w -> Bool) -> Bool
forAll set predicate = not $ thereExists set (not . predicate)

-- Range of a function in a given domain.
rangeOf :: (Eq y) => (x -> y) -> Set x -> Set y
rangeOf fn domain = Set $ \y -> thereExists domain $ \x -> y == fn x

unionAll :: Set (Set w) -> Set w
unionAll sets = Set $ \x -> thereExists sets $ \set -> x `member` set

intersectAll :: Set (Set w) -> Set w
intersectAll sets = Set $ \x -> forAll sets $ \set -> x `member` set

