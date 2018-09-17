{-# LANGUAGE FlexibleContexts #-}
module Gradient
  ( gradient
  , derivative
) where

import           Sets
import           Sequences
import           Analysis
import           Vectors
import           Functions
import Limits

import           Data.Maybe
import           Data.Proxy
import           GHC.TypeLits

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
-- Technically this is the "derivative error" where dx is our guess for the
-- actual derivative.
derivativeFn_
  :: (KnownNat n, Defined dom (RD n), Defined cod R1)
  => Fn dom (RD n) cod R1
  -> RD n
  -> RD n
  -> RD n
  -> R1
derivativeFn_ fn x dx h =
  Vec [norm2 (fn ⬅ (x |+| h) - fn ⬅ x - Vec [dx |.| h]) / norm2 h]

-- Given dx, compute the limit of the above function as h -> 0
limitDFN
  :: (KnownNat n, Defined dom (RD n), Defined cod R1)
  => Fn dom (RD n) cod R1
  -> RD n
  -> RD n
  -> Maybe ExtR1
limitDFN fn x dx = limitFn (safeBox $ derivativeFn_ fn x dx) zeroV

-- The gradient at a point is the vector that can push the limitDFN to 0.
gradient
  :: (KnownNat n, Defined dom (RD n), Defined cod R1)
  => Fn dom (RD n) cod R1
  -> RD n
  -> Maybe (RD n)
gradient fn x | interior (domain fn) x =
  singleton $ everything % \dx -> limitDFN fn x dx == (Just $ extend $ toR1 0)

-- Derivative is just gradient for R->R functions
derivative
  :: (Defined dom R1, Defined cod R1) => Fn dom R1 cod R1 -> R1 -> Maybe R1
derivative = gradient

-- Gradients are a useful concept in Machine Learning.

-- In general, it can be thought an operator that modifies a function.
-- In our limited definition it turns a scalar-valued function into a function
-- from the input space back to itself. The idea is that the original vector
-- and the gradient vector can be added together, which is the idea behind
-- gradient descent/ascent.
--
-- Now it's possible to add it incorrectly which results in the vector leaving
-- the original function's domain.
grad :: (KnownNat n, Defined dom (RD n), Defined cod R1) => Fn dom (RD n) cod R1 -> Fn dom (RD n) AllOf (RD n)
grad fn | valid fn = mustHave "already checked valid" $ box $ \x -> fromJust $ gradient fn x
  where 
    valid fn = forAll (domain fn) $ \x -> isJust (gradient fn x)

----------------------------------------------
--
-- The gradient of an expectation can be pushed inside the expectation of a
-- gradient (when some conditions are satisfied)
