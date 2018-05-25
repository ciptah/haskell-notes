-- Dedekind cuts.
-- https://en.wikipedia.org/wiki/Dedekind_cut

module Dedekind (
  rationals,
  isPartition,
  isCut,
  cuts,
  dedekindCuts,
  toOriginal,
  toReal
) where

import Sets
import Analysis
import Data.Maybe (fromJust)

rationals = Everything :: Set Rational

type Cut w = (Set w, Set w)

isPartition :: [Set a] -> Set a -> Bool
list `isPartition` set = and [ a /= empty | a <- list ] &&
  unionAll list == set && isPairwiseDisjoint list

isCut :: (Ord w) => (Set w, Set w) -> Set w -> Bool
isCut (a, b) set = 
  [a, b] `isPartition` set &&
  (forAll a $ \xa -> xa ∈ lowerBounds b) && -- partition implies xa /= any in b
  (upperBounds a ∩ a == empty) -- a contains no greatest element

-- While it's possible to define this in terms of partitions, it's
-- clearer to just directly define what a (Dedekind) cut is.
cuts :: (Ord w) => Set w -> Set (Cut w)
cuts set = Everything % \c -> isCut c set

dedekindCuts = cuts rationals

toOriginal :: (Ord w) => Cut w -> Maybe w
toOriginal (a, b) = singleton $ (lowerBounds b ∩ b)

-- All real numbers that are the lower bounds of the b-set
-- There is a supremum (the least upper bound)
toReal (a, b) = fromJust $ supremum $ reals % \x ->
  (forAll b $ \rat -> x <= rat)

isRealNumConstruction = dedekindCuts `equalCardinality` reals
