module Multivariate (
) where

-- https://downloads.haskell.org/~ghc/7.10.1/docs/html/users_guide/type-level-literals.html

import Sets
import SigmaAlgebra
import Probability
import Analysis
import Sequences

import Data.Maybe (fromJust, isJust)

-- We'll define aliases to distinguish against Observation.
type Observation = RealNum -- values emitted by the random variable.
