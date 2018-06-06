{-# LANGUAGE DataKinds #-}

module StochasticProcess (
  StochasticProcess,
  Filtration,
  process,
  sample,
  sampleInterval,
  realize,
  canMeasureRV,
  time,
  martingale,
  brownian
) where

import Sets
import Analysis
import SigmaAlgebra
import RandomVariable
import Multivariate
import Vector
import Expectation
import Sequences
import Probability (ProbabilitySpace)

import Data.Maybe (isJust, fromJust)

-- What is actually the "w" in a stochastic process? Trajectories.


-- Defining it like this makes explicit that there is only one probability
-- space defined for the entire process.
data StochasticProcess t w = Process {
  time :: Set t,
  getSPSpace :: (ProbabilitySpace w),
  getSPIndex :: (w -> t -> Vector 1 Observation)
}

-- Validate that the function at all times is a valid random variable.
process :: (Eq w) =>
  Set t -> ProbabilitySpace w -> (w -> t -> Vector 1 Observation)
  -> Maybe (StochasticProcess t w)
process tm psp idx = let candidate = Process tm psp idx in
  if valid candidate then Just candidate else Nothing
  where valid sp = forAll tm $ \t -> isJust $ makeRV psp (flip idx t)

sample :: (Eq w) => SP t w -> t -> RVD w 1
sample sp t = fromJust $ makeRV (getSPSpace sp) $ flip (getSPIndex sp) t

realize :: SP t w -> w -> (t -> Vector 1 Observation)
realize sp w = getSPIndex sp w

instance Eq (StochasticProcess t w) where
  sp1 == sp2 = error "TODO"

type SP = StochasticProcess

type Filtration t w = t -> SigmaAlgebra w
-- TODO: check filtration

-- X_t - X_s
sampleInterval :: SP t w -> t -> t -> RVD w 1
sampleInterval = error "TODO!"

---------- Martingale property of Continuous-time 1D SPs ----------------

canMeasureRV :: SigmaAlgebra w -> RVD w n -> Bool
canMeasureRV sa rv = forAllSets borelRd $ \event ->
  sa `canMeasure` (RandomVariable.lookup rv event)

realTime = (Everything :: Set RealNum) % \t -> t > 0
realTimeSPs = (Everything) % \sp -> time sp == realTime

martingale :: (Eq w) => Filtration RealNum w -> SP RealNum w -> Bool
martingale f sp = let sptime = time sp in
  (sptime == realTime) &&
  -- X_t is F_t measurable
  (forAll sptime $ \t -> (f t) `canMeasureRV` (sample sp t)) &&
  -- E|X_t| is finite
  (forAll sptime $ \t -> finite $ limExp (absolute $ sample sp t)) &&
  -- Conditional expectation becomes random variable
  (forAll sptime $ \t -> forAll (sptime % (<= t)) $ \s ->
    conditionalOnSigmaAlgebra (sample sp t) (f s) == sample sp s)
  where finite (Finite _) = True
        finite _ = False
        absolute rv = KnownRV $ (vmap abs) <. rv -- :: Univariate

----------------- Brownian Motion ------------------------

brownian :: (Eq w) => SP RealNum w
brownian = fromJust $ singleton $ realTimeSPs % \sp ->
  -- Independence of intervals
  (forAll (intervalList sp) $ \i ->
    and [di == dj || independent (i !! di) (i !! dj) |
          di <- [0..((length i) - 1)],
          dj <- [0..((length i) - 1)]]) &&
  -- Normal distribution of intervals
  (forAll (time sp) $ \t -> forAll (time sp % (< t)) $ \s ->
    -- The mapping is necessary because `normal` is on RealNum
    -- While intervals are of type (Vector 1 RealNum)
    KnownRV ((@@ 0) <. sampleInterval sp t s) == normal 0 (t - s)) &&
  -- All trajectories are continuous
  (forAll Everything $ \w -> isContinuous $ realize sp w)

  where intervalList sp = error "list of disjoint RVs from intervals"
        isContinuous fn = error "TODO!"

-------------------- First passage and running max -----------------


-- RunningMax of SP up to t
runMax :: (Eq w) => SP RealNum w -> w -> RealNum -> Vector 1 Observation
runMax sp w t = fromJust $ supremum values
  where trajectory = realize sp w
        interval = time sp % \tt -> tt <= t
        values = smap trajectory interval

-- The output is another random variable.
-- Implicitly this also means that the sample space of the process has to
-- be the same for all time t.
runningMax :: (Eq w) => SP RealNum w -> SP RealNum w
runningMax sp = fromJust $ process (time sp) (getSPSpace sp) $ runMax sp

  

