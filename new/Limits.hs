{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Limits (
  limitFn,
  continuousAt,
  gradient,
  derivative
) where

import Sets
import Sequences
import Analysis
import Vectors
import Functions

import Data.Maybe
import Data.Proxy
import GHC.TypeLits

-- Proposition 6.3. The limit of a function is unique if it exists
limitFn :: (Defined dom (RD n), Defined cod (RD m),
            KnownNat n, KnownNat m) =>
  Fn dom (RD n) cod (RD m) -> RD n -> Maybe (ConvRD m)
limitFn fn target | accumulation (domain fn) target =
  coalesce $ singleton $
    -- Apply the function to the approaches, and analyze convergence. Do not
    -- collapse the Maybe because if "Nothing" exists that indicates some path
    -- with undefined convergence, which changes the answer!
    smap limit $ smap (fn <.) $
    -- Only consider approaches within the domain of the function
    collapse $ smap (\seq -> box (f seq)) $
    -- Find all approaches to the target
    approaches $ convRd $ Finite target
  where coalesce Nothing = Nothing
        coalesce (Just x) = x

continuousAt
  :: (KnownNat n, KnownNat m, Defined dom (RD n), Defined cod (RD m))
     => Fn dom (RD n) cod (RD m) -> RD n -> Bool
continuousAt fn target
  | isolated (domain fn) target = True
  | accumulation (domain fn) target =
    limitFn fn target == (Just $ convRd $ Finite $ fn ← target)

-------------- Derivative/Differentiable ---------------------


-- The gradient of f is defined as the unique vector field whose dot product
-- with any unit vector v at each point x is the directional derivative of f
-- along v.
-- * For now, let's only consider gradients of the interior points of the domain
--   because dealing with boundaries is a PITA.

directions :: Proxy n -> Direction (RD n)
directions p = Everything

-- https://en.wikipedia.org/wiki/Gradient#Gradient_as_a_derivative
-- http://mathworld.wolfram.com/DirectionalDerivative.html
-- https://math.stackexchange.com/questions/372070/f-not-differentiable-at-0-0-but-all-directional-derivatives-exist

-- Given x and candidate gradient dx, and some delta vector h,
-- compute (f(x + h) - f(x) - dx . h) / h
-- The wiki article uses Rm -> Rn, here we use Rn -> Rm
derivativeFn_ :: (KnownNat n, Defined dom (RD n), Defined cod R1)
  => Fn dom (RD n) cod R1 -> RD n -> RD n -> RD n -> R1
derivativeFn_ fn x dx h =
  Vec [norm2 (fn ← (x |+| h) - fn ← x - Vec [dx |.| h]) /  norm2 h]

-- Given dx, compute the limit of the above function as h -> 0
limitDFN :: (KnownNat n, Defined dom (RD n), Defined cod R1)
  => Fn dom (RD n) cod R1 -> RD n -> RD n -> Maybe (ConvRD 1)
limitDFN fn x dx = limitFn (safeBox $ derivativeFn_ fn x dx) zeroV

-- The gradient is the vector that can push the limitDFN to 0.
gradient :: (KnownNat n, Defined dom (RD n), Defined cod R1)
  => Fn dom (RD n) cod R1 -> RD n -> Maybe (RD n)
gradient fn x | interior (domain fn) x = singleton $ everything %
  \dx -> limitDFN fn x dx == (Just $ convRd $ Finite $ toR1 0)

-- Derivative is just gradient for R->R functions
derivative :: (Defined dom R1, Defined cod R1)
  => Fn dom R1 cod R1 -> R1 -> Maybe R1
derivative = gradient

-- Interesting that we haven't linked this definition with integrals yet.
-- That is, this isn't enough to compute the probability density function
-- of a distribution.

