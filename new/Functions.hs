{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Functions(
  Fn,
  domain,
  codomain,
  f, (←),
  fnEquals,
  clip, box,
  preimage, preimageOf, range,onto, one2one, bijective,
  (<.),

  RealFn, TimeFn, PositiveFn, ZeroOneFn, Sequence
) where

import Sets
import Data.Maybe

-------------- Definition & Accessors ------------------

data Fn dom a cod b = Fn (a -> b) (dom a) (cod b)

domain :: (Defined dom a) => Fn dom a cod b -> dom a
domain (Fn _ dom _) = dom

codomain :: (Defined cod b) => Fn dom a cod b -> cod b
codomain (Fn _ _ cod) = cod

f :: (Defined dom a, Defined cod b) => Fn dom a cod b -> a -> b
f (Fn fn dom cod) x | x ∈ dom && (fn x) ∈ cod = fn x

infixr 9 ← -- u2190
fn ← x = f fn x

-------------- Instantiations ------------------

-- Validation for functions.
instance (Defined dom a, Defined cod b) => Defined AllOf (Fn dom a cod b) where
  candidate _ fn = -- Validate domain, codomain and f agree on function
    forAll (domain fn) $ \x -> fn ← x ∈ codomain fn

-- Generalized equals works when functions have different representations
-- for domain and codomain, i.e. (Everything :: AllOf RealNum) === Subset True
fnEquals ::
    (Defined dom1 a,
     Defined dom2 a,
     Defined cod1 b,
     Defined cod2 b,
     Eq b)
    => Fn dom1 a cod1 b -> Fn dom2 a cod2 b -> Bool
fnEquals f1 f2 =
    domain f1 === domain f2 && codomain f1 === codomain f2 &&
    (forAll (domain f1) $ \x -> f f1 x == f f2 x)

instance (
    Defined dom a, Defined AllOf a, Defined cod b, Defined AllOf b, Eq b
    ) => Eq (Fn dom a cod b) where
  f1 == f2 = f1 `fnEquals` f2

-------------- Construction from raw functions. ------------------

-- Clip a raw function into the given domain and codomain.
-- Might not work if the function is undefined in some part of the domain.
clip :: (Defined dom a, Defined cod b, Eq b)
  => (a -> b) -> dom a -> cod b -> Maybe (Fn dom a cod b)
clip fn dom cod = if valid ffn then Just ffn else Nothing
  where ffn = (Fn fn dom cod)

box :: (Defined dom a, Defined cod b, Eq b)
  => (a -> b) -> Maybe (Fn dom a cod b)
-- To make a "raw" Haskell fn well-defined, pick the unique function that has
-- the desired domain and codomain, that has the same behavior as fn within
-- the domain (assuming fn is defined everywhere in the domain)
box fn = singleton $ everything % \ffn ->
    (forAll (domain ffn) $ \x -> fn x == f ffn x)

-------------- Imaging/range. ------------------

preimage :: (Defined dom a, Defined cod b, Defined set b)
  => Fn dom a cod b -> set b -> Subset a
preimage fn target = everything % \x -> fn ← x ∈ target

-- Same of above but only for a single value.
preimageOf :: (Defined dom a, Defined cod b, Eq b)
  => Fn dom a cod b -> b -> Subset a
preimageOf fn target = preimage fn $ singletonOf target

-- Range is the subset of codomain that is reachable by the function.
range :: (Eq b, Defined dom a, Defined cod b) => Fn dom a cod b -> Subset b
range fn = smap (f fn) (domain fn)

onto :: (Eq b, Defined cod b, Defined dom a) => Fn dom a cod b -> Bool
onto fn = range fn === codomain fn

-- x1, x2 ∈ X and x1 /= x2 implies that f(x1) /= f(x2).
-- forAll (domain ⨯ domain) $ \(x1 x2) -> if x1 /= x2 then f x1 /= f x2 e. F.
one2one :: (Eq b, Defined cod b, Defined dom a) => Fn dom a cod b -> Bool
one2one fn = -- Alternative way of saying it.
  forAll (codomain fn) $ \y -> isSingleton $ preimageOf fn y

bijective :: (Eq b, Defined cod b, Defined dom a) => Fn dom a cod b -> Bool
bijective fn = one2one fn && onto fn

-------------- Composition ---------------------

-- Be careful!!
-- For "Set" types, i.e. singleton types with only Everything, this is 
-- guaranteed to produce a function. However when the set type isn't singleton
-- (subsets, open balls), it can be problematic. I'll allow it with the
-- understanding that it could fail to turn up a function.
(<.) :: (Defined dom a, Defined cod1 b, Defined cod2 c)
  => Fn cod1 b cod2 c -> Fn dom a cod1 b -> Fn dom a cod2 c
f2 <. f1 | valid candidate = candidate
  where candidate = Fn (f f2 . f f1) (domain f1) (codomain f2)

-------------- Examples ---------------------

type RealFn dom a = Fn dom a AllOf RealNum -- A->R functions.
type TimeFn cod b = Fn NonNegative RealNum cod b -- Functions with R>=0 domain

-- Functions to the positive reals (like for example a density function)
type PositiveFn dom a b = Fn dom a Positive b

-- Functions to the [0, 1] Real interval (like a Probability measure, or RV)
type ZeroOneFn dom a = Fn dom a ZeroOne RealNum

-- Sequences are functions from integers.
type Sequence cod b = Fn Positive Integer cod b

instance (Defined set1 a, Defined set2 b, Ord a, Ord b)
    => Defined Increasing (Fn set1 a set2 b) where
  candidate _ fn = forAll everything $ \(x1, x2) -> 
    x1 ∈ domain fn && x2 ∈ domain fn &&
    if x1 < x2 then f fn x1 < f fn x2 else True

instance (Defined set1 a, Defined set2 b, Ord a, Ord b)
    => Defined NonDecreasing (Fn set1 a set2 b) where
  candidate _ fn = forAll everything $ \(x1, x2) -> 
    x1 ∈ domain fn && x2 ∈ domain fn &&
    if x1 < x2 then f fn x1 <= f fn x2 else True
