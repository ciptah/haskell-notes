-- https://www.math.ucdavis.edu/~hunter/intro_analysis_pdf/intro_analysis.pdf

module Analysis (
  image, -- aka range
  preimage,
  onto,
  upperBounds,
  lowerBounds,
  sup, inf
) where

import Sets

type RealNum = Double

-- Domain, Codomain, Function, Range
image :: (Eq b) => Set a ->(a -> b) -> Set b -> Set b
image domain fn codomain =
    codomain % \y -> thereExists domain $ \x -> (fn x) == y

-- Find the preimage of a set in the codomain under the function.
preimage :: (Eq b) => Set a -> (a -> b) -> Set b -> Set a
preimage domain fn image = domain % \x -> fn x `member` image

-- A function is onto if its range is all of Y
onto :: (Eq b) => Set a -> (a -> b) -> Set b -> Bool
onto domain fn codomain = (image domain fn codomain) == codomain

data BoundType = Upper | Lower

-- Upper/lower bounds
bounds :: BoundType -> Set RealNum -> Set RealNum
bounds bt set = Reals % \r -> forAll set $ \x -> r `bounds` x
    where bounds = boundFor bt
          boundFor Upper = (>=) -- r >= x
          boundFor Lower = (<=) -- r <= x
upperBounds = bounds Upper
lowerBounds = bounds Lower

-- Sup: Get the one value from all upper bounds that's less than all other
-- upper bounds.
sup :: Set RealNum -> Maybe RealNum
sup set = singleton $ b % \x -> forAll b $ \y -> x <= y -- least upper bound
    where b = upperBounds set

inf :: Set RealNum -> Maybe RealNum
inf set = singleton $ b % \x -> forAll b $ \y -> x >= y -- most lower bound
    where b = lowerBounds set
