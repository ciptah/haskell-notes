{-# LANGUAGE ExistentialQuantification #-}
-- Set theory formalized in Haskell.

module Sets (
  Set(Everything, Subset),
  Statement,
  (%),
  Collection,
  RealNum,
  reals, r1, integers, r2, nonnegatives, naturals,
  member, notMember, (∈), (∉), -- u2208, u2209
  thereExists', forAll', eval, prove, thereExists, forAll,
  intersect, union, minus, complement
  -- isEmpty,
  -- isSubsetOf,
  -- minus,
  -- union,
  -- forAll,
  -- unionAll,
  -- asList,
  -- fromList,
  -- isDisjoint,
  -- isAllDisjoint,
  -- star,
  -- countableUnions,
  -- singleton,
) where

import Data.Maybe (Maybe)

-- A (mathematical) set of x.
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



-- Some examples.
reals = Everything :: Set RealNum
r1 = reals
integers = Everything :: Set Integer
r2 = Everything :: Set (RealNum, RealNum)
nonnegatives = integers % \i -> i >= 0 -- non-negative integers.
naturals = integers % \i -> i > 0 -- natural numbers
empty = Everything % \x -> False -- empty set.



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
eval (Exists inSet predicate) = error "Uncomputable!!"

-- Exists statements can be proven, if you supply a satisfying element
prove (Exists inSet predicate) proof =
    if proof ∈ inSet && predicate proof then "QED" else error "Doh!!"

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

--
--
-- -- Mathematical "For all"
-- forAll :: (Foldable t) => t a -> (a -> Bool) -> Bool
-- forAll s pred = foldr (\x z -> (pred x) && z) True s
--
-- -- Mathematical "There Exists"
-- thereExists :: (Foldable t) => t a -> (a -> Bool) -> Bool
-- thereExists s pred = foldr (\x z -> (pred x) || z) False s
--
-- instance Show (Set a) where
--   show EmptySet = "{}"
--   show x = error "Not Implemented"
--
-- instance Eq (Set a) where
--   (==) EmptySet EmptySet = True
--   (==) x y = error "Not Implemented"
--
-- instance Foldable Set where
--   foldr f z EmptySet = z
--   foldr f z s = error "Not implemented"
--
-- instance Functor Set where
--   fmap fn EmptySet = EmptySet
--   fmap fn set = error "Not implemented"
--
-- -- Declare all the common set operations.
--
-- isEmpty :: Set a -> Bool
-- isEmpty EmptySet = True
-- isEmpty _ = False
--
--
-- isSubsetOf :: Set a -> Set a -> Bool
-- isSubsetOf EmptySet _ = True
-- isSubsetOf _ _ = error "Not implemented"
--
-- minus :: (Eq a) => Set a -> Set a -> Set a
-- minus EmptySet _ = EmptySet
-- minus x EmptySet = x
-- minus x y | x == y = EmptySet
-- minus _ _ = error "Not implemented"
--
-- union :: Set a -> Set a -> Set a
-- union = error "Not implemented"
--
-- intersect :: Set a -> Set a -> Set a
-- intersect = error "Not implemented"
--
-- unionAll :: [Set a] -> Set a
-- unionAll sets = foldr (union) EmptySet sets
--
-- asList :: Set a -> [a]
-- asList EmptySet = []
-- asList _ = error "Not implemented"
--
-- fromList :: [a] -> Set a
-- fromList [] = EmptySet
-- fromList _ = error "Not implemented"
--
-- -- Disjoint, aka no intersection.
-- isDisjoint :: (Eq a) => Set a -> Set a -> Bool
-- isDisjoint x y = x `intersect` y == EmptySet
--
-- -- Are all the sets in the given list disjoint with one another?
-- isAllDisjoint :: (Eq a) => [Set a] -> Bool
-- isAllDisjoint sets = forAll cartesianProduct $ \(x, y) -> x `isDisjoint` y
--     where cartesianProduct = [ (x, y) | x <- sets, y <- sets ]
--
-- -- From a set S = {a, b, c, ...}
-- -- Build a set S* = {0, a, b, c, ..., aa, ab, ac, ..., }
-- -- Also known as a Kleene star.
-- -- This is intentionally a list, so aaba /= aba /= baaa
-- star :: Set a -> Set [a]
-- star set = fromList result
--     where result = [ add:cur | cur <- []:result, add <- (asList set) ]
--
-- -- Given a set of sets, return a sequence of sets made of the countable
-- -- unions of the elements in the set.
-- countableUnions :: Collection (Set a) -> Set (Set a)
-- countableUnions sets = fmap unionAll $ star sets
--
-- -- Unpack: If singleton, output inner value. Otherwise, None.
-- singleton :: Set a -> Maybe a
-- singleton (Singleton x) = Just x
-- singleton _ = Nothing
