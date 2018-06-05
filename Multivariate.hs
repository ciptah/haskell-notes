{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Multivariate (
  Conditional,
  Joint,
  Univariate,
  RVD,
  condition,
  marginalize,
  connect,
  join,
  independent
) where

import GHC.TypeLits
import Data.Proxy

import RandomVariable
import Vector
import Sets ((∩))
import Probability (probability)

type Joint w n = Distribution w (Vector n Observation)

type Univariate w = Joint w 1

-- Random variable in D dimensions
type RVD w n = RandomVariable w (Vector n Observation)

-- Conditional distribution from m to r variables.
type Conditional w (m :: Nat) (r :: Nat) =
  Vector m Observation -> Distribution w (Vector r Observation)

using :: String
using = error "eh!"

-- Split a distribution into marginal and conditional.
condition :: Joint w n -> Selection m n -> Conditional w m (n - m)
condition = error "TODO"

marginalize :: Joint w n -> Selection m n -> Joint w m
marginalize = error "TODO"

-- Here's a definition for "join" that relies on conditionals.
connect :: Joint w m -> Conditional w m r -> Joint w (m + r)
connect = error "TODO"

-- But what exactly does it mean to "find the joint?"
-- Remember that _there is only ever one probability space_, and the measure
-- P is the "source of truth". So we could define the joint as the
-- preimage intersection.
join_ :: (KnownNat m, KnownNat r, Eq w) =>
  Joint w m -> Joint w r -> Proxy m -> Proxy r -> Joint w (m + r)
join_ d1 d2 proxy1 proxy2
  | ps d1 /= ps d2 = error "Incompatible!"
  | using == "Event Intersection" =
  -- Find event where the "RV1 part" matches.
  -- Find event where the "RV2 part" matches.
  -- Take intersection, and compute the probability.
    UnknownRV $ \event -> probability (ps d1) $
      RandomVariable.lookup rv1 (project event sel1) ∩
      RandomVariable.lookup rv2 (project event sel2)
  where ps dist = getRVSpace $ toRV dist
        rv1 = toRV d1
        rv2 = toRV d2
        sel1 = sel [0..(fromIntegral $ natVal proxy1)]
        sel2 = sel [0..(fromIntegral $ natVal proxy2)]

join :: (KnownNat m, KnownNat r, Eq w)  =>
  Joint w m -> Joint w r -> Joint w (m + r)
join d1 d2 = join_ d1 d2 Proxy Proxy


-- Two RVs in the same prob. space are independent
independent :: Joint w m -> Joint w r -> Bool
independent = error "TODO!"
