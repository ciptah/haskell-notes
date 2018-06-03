module StochasticProcess (
  StochasticProcess,
) where

import RandomVariable
import Multivariate
import Vector

-- What is actually the "w" in a stochastic process?
-- Usually we just get the pmf/pdf indexed at time t.
-- But for completeness maybe we should "imagine" what the w looks like.

-- data StochasticProcess w = (Ord time) => Process (time -> RandomVariable w)

-- Maybe the sample space is (a subset) of functions form time to R?
-- Not really, because it could be anything.
--
-- So maybe defining RPs in terms of RVs is a little to abstract and we should
-- instead define it as a function from time to the "distribution function"
-- at time t.

-- Note that the type of "time" has no bearing on the values of the RV
-- So it is possible to have a continuous-time-discrete-state SP, and v. versa

-- Think of the chain of objects this "w" has to pass through to get here:
--   Set w -> SigmaAlgebra w -> ProbabilityMeasure w -> RandomVariable w
--     -> Distribution w -> StochasticProcess w

data StochasticProcess t w = Process (t -> Univariate w)

sample :: StochasticProcess t w -> t -> Univariate w
sample (Process index) t = index t

realize :: StochasticProcess t w -> w -> (t -> Observation)
realize (Process fn) w = \t -> (getRVFunction $ toRV $ fn t) w @@ 0

