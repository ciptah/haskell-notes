module StochasticProcess (
  StochasticProcess,
  Filtration,
  sample,
  realize,
  martingale
) where

import Sets
import SigmaAlgebra
import RandomVariable
import Multivariate
import Vector
import Expectation
import Sequences

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

type SP = StochasticProcess

type Filtration t w = t -> SigmaAlgebra w
-- TODO: check filtration

sample :: SP t w -> t -> Univariate w
sample (Process index) t = index t

realize :: SP t w -> w -> (t -> Observation)
realize (Process fn) w = \t -> (getRVFunction $ toRV $ fn t) w @@ 0

---------- Martingale property of Continuous-time 1D SPs ----------------

rvMeasurable :: SigmaAlgebra w -> RVD w n -> Bool
rvMeasurable sa rv = forAllSets borelRd $ \event ->
  sa `canMeasure` (RandomVariable.lookup rv event)

martingale :: (Eq w) => Filtration RealNum w -> SP RealNum w -> Bool
martingale f sp = let time = (Everything :: Set RealNum) % \t -> t > 0 in
  -- X_t is F_t measurable
  (forAll time $ \t -> rvMeasurable (f t) (rv t)) &&
  -- E|X_t| is finite
  (forAll time $ \t -> finite $ limExp (absolute $ rv t)) &&
  -- Conditional expectation becomes random variable
  (forAll time $ \t -> forAll (time % (<= t)) $ \s ->
    conditionalOnSigmaAlgebra (rv t) (f s) == rv s)
  where rv t = toRV $ sample sp t
        finite (Finite _) = True
        finite _ = False
        absolute rv = KnownRV $ (vmap abs) <. rv -- :: Univariate


