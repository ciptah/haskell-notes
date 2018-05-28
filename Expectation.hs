module Expectation (
) where

import Sets
import Analysis
import Sequences
import RandomVariable
import Probability

import Data.Maybe (fromJust, isJust)

-- For single-valued random variables, either discrete or continuous.
expectation :: (Eq a) => Distribution a -> (Observation -> Likelihood) -> RealNum
expectation dist fn | isJust $ distPmf =
  sum $ map (\x -> fn x * (fromJust distPmf) x) $
    fromJust $ toList $ domain $ Box (fromJust distPmf) Everything
  where distPmf = pmf dist
