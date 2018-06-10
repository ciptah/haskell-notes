{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Limits (
  limitFn,
  continuousAt
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

directions :: Proxy n -> Direction (RD n)
directions p = Everything

-- Given x and direction dx (must be length 1 centered at 0), get a function
-- from positive h to df/dh value
derivativeFn_ :: (KnownNat n, Defined dom (RD n), Defined cod R1)
  => Proxy n -> Fn dom (RD n) cod R1 -> RD n -> RD n -> Fn Subset R1 AllOf R1
derivativeFn_ p fn x dx | valid dx = safeBox $ \vh -> let h = vh @@ 0 in
  if h > 0 then Vec [(ffn ← (x |+| h *| dx) - ffn ← x) / h]
  else error "Invalid"
  where ffn = (@@ 0) <<. fn
        valid dx = dx ∈ directions p

-- Function from direction to directional derivative (rate of change)
directionalDerivative
  :: (KnownNat n, Defined dom (RD n), Defined cod R1) =>
     Fn dom (RD n) cod R1 -> RD n -> Fn Direction (RD n) AllOf (Maybe (ConvRD 1))
directionalDerivative fn x = fromJust $ box $ \dx ->
  limitFn (derivativeFn_ Proxy fn x dx) zeroV -- limit h -> 0

onlyFinites :: Subset (Maybe (ConvRD 1)) -> Subset (RD 1)
onlyFinites subset = collapse $ smap change subset
  where change (Just (Finite x)) = Just x
        change _ = Nothing

-- https://en.wikipedia.org/wiki/Gradient#Gradient_as_a_derivative
gradientDirection
  :: (KnownNat n, Defined dom (RD n), Defined cod R1) =>
     Fn dom (RD n) cod R1 -> RD n -> Maybe (RD n)
gradientDirection fn x | isJust maxDer =
  singleton $ preimage dder $ singletonOf $ maxDer
  where dder = directionalDerivative fn x -- direction (unit length) -> deriv
        maxDer = supremum $ onlyFinites $ range dder -- Maximum value of DirDer
        maxConvDer = Just (\x -> convRd x) <*> maxDer
gradientDirection fn x | otherwise = Nothing

gradient fn x = if isJust gdir then (Just $ dder *| fromJust gdir) else Nothing
  where gdir = gradientDirection fn x
        dderv | isJust gdir = (directionalDerivative fn x) ← fromJust gdir
        dder | isJust gdir = fin $ (fromJust dderv) @@ 0
        fin (Finite x) = x

