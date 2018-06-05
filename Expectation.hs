module Expectation (
  expectation,
  limExp,
  conditionalOnSigmaAlgebra
) where

import Sets
import Sequences
import Vector
import RandomVariable
import Probability
import Multivariate
import SigmaAlgebra

import Data.Maybe (fromJust, isJust)

expectation :: Joint w n -> Vector n Observation
expectation = error "TODO" -- Use Lebesgue Integral

-- Same as above but formulated as a limit, which lets 
limExp :: Joint w n -> Convergence (Vector n Observation)
limExp = error "TODO" -- Use Lebesgue Integral

-- A sub-sigma-algebra has the same empty set and "full" set, but their
-- granularity is different. I.e. the sub cannot answer some queries about
-- certain events that are too specific

-- Conditional expectation wrt sub sigma-algebra (most general)
-- What comes out is a random variable
-- This random variable always exists and is unique
-- https://en.wikipedia.org/wiki/Conditional_expectation
-- https://www.math.purdue.edu/~stindel/teaching/ma539/cdt-expectation-2.pdf
conditionalOnSigmaAlgebra :: RVD w n -> SigmaAlgebra w -> RVD w n
conditionalOnSigmaAlgebra = error "TODO"
