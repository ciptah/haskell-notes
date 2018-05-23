-- Set theory formalized in Haskell.
-- Not meant to be fast (or be actually run), it's just to make things formal.
--
-- Uses this heavily:
-- https://wiki.haskell.org/Smart_constructors

module Sets (
  Set,
  EmptySet
) where

-- A (mathematical) set of x.
data Set x = EmptySet | ASet [x]

-- Constructor.
set :: (Eq x) => [x] -> Set x
set [] = EmptySet
set any = ASet any
