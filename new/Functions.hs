{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Functions(
  Fn
) where

import Sets
import Data.Maybe

-------------- Definition & Accessors ------------------

data Fn (dom :: * -> *) a (cod :: * -> *) b = Fn (a -> b) (dom a) (cod b)

domain :: (Defined dom a) => Fn dom a cod b -> dom a
domain (Fn _ dom _) = dom

codomain :: (Defined cod b) => Fn dom a cod b -> cod b
codomain (Fn _ _ cod) = cod

f :: (Defined dom a, Defined cod b) => Fn dom a cod b -> a -> b
f (Fn fn dom cod) x | x ∈ dom && (fn x) ∈ cod = fn x

infixl 9 ← -- u2190
fn ← x = f fn x

-------------- Instantiations ------------------

-- Validation for functions.
instance (Defined dom a, Defined cod b) => Defined AllOf (Fn dom a cod b) where
  contains _ fn = -- Validate domain, codomain and f agree on function
    forAll (domain fn) $ \x -> fn ← x ∈ codomain fn

-- Generalized equals works when functions have different representations
-- for domain and codomain, i.e. (Everything :: AllOf RealNum) === Subset True
fnEquals :: 
    (Defined dom1 a,
     Defined dom2 a,
     Defined AllOf a,
     Defined cod1 b,
     Defined cod2 b,
     Defined AllOf b,
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
clip fn dom cod = if valid candidate then Just candidate else Nothing
  where candidate = (Fn fn dom cod)

box :: (
    Defined dom a, Defined AllOf a, Defined cod b, Defined AllOf b, Eq b
  ) => (a -> b) -> Maybe (Fn dom a cod b)
-- To make a "raw" Haskell fn well-defined, pick the unique function that has
-- the desired domain and codomain, that has the same behavior as fn within
-- the domain (assuming fn is defined everywhere in the domain)
box fn = singleton $ everything % \ffn ->
    (forAll (domain ffn) $ \x -> fn x == f ffn x)

type RealFn = Fn AllOf RealNum AllOf RealNum
type TimeFn = Fn Positive RealNum AllOf RealNum
