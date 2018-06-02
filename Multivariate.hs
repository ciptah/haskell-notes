{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Multivariate (
  Conditional,
  Selection,
  condition,
  marginalize,
  connect,
  join
) where

import GHC.TypeLits

import RandomVariable
import Vector

type Joint w n = Distribution w (Vector n Observation)

-- Select m unique things from 0..n-1
data Selection (m :: Nat) (n :: Nat) = Select (Vector m Integer)

-- Conditional distribution from m to r variables.
type Conditional w (m :: Nat) (r :: Nat) =
  Vector m Observation -> Distribution w (Vector r Observation)

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
join :: Joint w m -> Joint w r -> Joint w (m + r)
join = error "TODO!"
--join d1 d2 | ps1 != ps2 = error "Incompatible!"
--           | otherwise = error "TODO!" -- UnknownRV makeJoint rv1 rv2
