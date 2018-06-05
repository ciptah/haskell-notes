{-# LANGUAGE DataKinds #-}

module StochasticProcess (
  StochasticProcess,
  Filtration,
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

import Data.Maybe (fromJust)

-- What is actually the "w" in a stochastic process? Realizations.

data StochasticProcess t w = Process (t -> RVD w 1)

instance Eq (StochasticProcess t w) where
  (Process f1) == (Process f2) = Box f1 Everything == Box f2 Everything

type SP = StochasticProcess

type Filtration t w = t -> SigmaAlgebra w
-- TODO: check filtration

sample :: SP t w -> t -> RVD w 1
sample (Process index) t = index t

-- X_t - X_s
sampleInterval :: SP t w -> t -> t -> RVD w 1
sampleInterval = error "TODO!"

realize :: SP t w -> w -> (t -> Observation)
realize sp w = \t -> (getRVFunction $ sample sp t) w @@ 0

---------- Martingale property of Continuous-time 1D SPs ----------------

canMeasureRV :: SigmaAlgebra w -> RVD w n -> Bool
canMeasureRV sa rv = forAllSets borelRd $ \event ->
  sa `canMeasure` (RandomVariable.lookup rv event)

time = (Everything :: Set RealNum) % \t -> t > 0

martingale :: (Eq w) => Filtration RealNum w -> SP RealNum w -> Bool
martingale f sp =
  -- X_t is F_t measurable
  (forAll time $ \t -> (f t) `canMeasureRV` (sample sp t)) &&
  -- E|X_t| is finite
  (forAll time $ \t -> finite $ limExp (absolute $ sample sp t)) &&
  -- Conditional expectation becomes random variable
  (forAll time $ \t -> forAll (time % (<= t)) $ \s ->
    conditionalOnSigmaAlgebra (sample sp t) (f s) == sample sp s)
  where finite (Finite _) = True
        finite _ = False
        absolute rv = KnownRV $ (vmap abs) <. rv -- :: Univariate

----------------- Brownian Motion ------------------------

brownian :: (Eq w) => SP RealNum w
brownian = fromJust $ singleton $ Everything % \sp ->
  -- Independence of intervals
  (forAll (intervalList sp) $ \i ->
    and [di == dj || independent (i !! di) (i !! dj) |
          di <- [0..((length i) - 1)],
          dj <- [0..((length i) - 1)]]) &&
  -- Normal distribution of intervals
  (forAll time $ \t -> forAll (time % (< t)) $ \s ->
    -- The mapping is necessary because `normal` is on RealNum
    -- While intervals are of type (Vector 1 RealNum)
    KnownRV ((@@ 0) <. sampleInterval sp t s) == normal 0 (t - s)) &&
  -- All trajectories are continuous
  (forAll Everything $ \w -> isContinuous $ realize sp w)

  where intervalList sp = error "list of disjoint RVs from intervals"
        isContinuous fn = error "TODO!"
  

