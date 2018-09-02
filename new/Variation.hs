-- Bounded variation, total variation, quadratic variation of R->R functions.
-- https://en.wikipedia.org/wiki/Total_variation
-- https://en.wikipedia.org/wiki/P-variation
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Variation (
  variation,
  totalVariation,
  quadraticVariation,
  boundedVariation
) where

import Sets
import Vectors
import Analysis
import Integral
import Functions
import FunctionSpaces
import Sequences

-------------- Variation between two endpoints. ---------------------

variationTerm_ :: RealNum -> Fn AllOf R1 AllOf R1 -> Segment R1 -> Subset R1 -> ExtR1
variationTerm_ p fn over interval =
  extend $ pow p $ (fn ⬅ end) - (fn ⬅ start)
  where end = mustHave "well-def." $ supremum $ interval ∩ over
        start = mustHave "well-def." $ infimum $ interval ∩ over

variationSum_ :: RealNum -> Fn AllOf R1 AllOf R1 -> Segment R1 -> Partition -> ExtR1
variationSum_ p fn over partition =
  sumSeq $ (variationTerm_ p fn over) <<. partition

variation :: RealNum -> Fn AllOf R1 AllOf R1 -> Segment R1 -> ExtR1
variation p fn over =
  mustHave "ExtR1 is complete" $
    supremum $ smap (variationSum_ p fn over) finiteMeshPartitions

totalVariation = variation 1
quadraticVariation = variation 2

-- A real-valued function {\displaystyle f} f on the real line is said to be of
-- bounded variation (BV function) on a chosen interval [a, b]⊂ℝ if its total
-- variation is finite
boundedVariation fn over = justFinite $ Just $ totalVariation fn over
