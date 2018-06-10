{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SigmaAlgebra (
) where

import Sets

data SigmaAlgebra w = SigmaAlgebra {
  outcomes :: Subset w,
  events :: Subset (Subset w)
}

-- Define the validity of all sigma-algebra constructions.
-- The SA must be self-consistent.
instance (Defined AllOf w, Eq w) => Defined AllOf (SigmaAlgebra w) where
  candidate _ sa = and [
    -- Events must be subsets of the sample set.
    forAll (events sa) $ \ev -> ev ⊆ outcomes sa,
    -- Includes empty set.
    empty ∈ events sa,
    -- Closed under complement.
    forAll (events sa) $ \ev -> (outcomes sa `minus` ev) ∈ events sa,
    -- Closed under countable unions.
    forAll (countableUnions $ events sa) $ \union -> union ∈ events sa]
