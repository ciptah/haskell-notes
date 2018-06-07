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

data Fn (domain :: * -> *) a (codomain :: * -> *) b = Fn (a -> b)

-- This is just for type hint
dom_ :: Fn dom a cod b -> dom a
dom_ = error "Undefined"

cod_ :: Fn dom a cod b -> cod b
cod_ = error "Undefined"

domain :: (Defined dom a, Defined AllOf a) => Fn dom a cod b -> SomeSet a
domain fn = everything % \x -> x ∈ (dom_ fn) 

codomain :: (Defined cod b, Defined AllOf b) => Fn dom a cod b -> SomeSet b
codomain fn = everything % \x -> x ∈ (cod_ fn) 

instance (
    Defined dom a, Defined AllOf a, Defined cod b, Defined AllOf b
    ) => Defined AllOf (Fn dom a cod b) where
  contains _ ffn@(Fn fn) = -- Make sure fn is compatible with decl. dom, cod
    forAll (domain ffn) $ \x -> (fn x) ∈ (codomain ffn)

-- Evaluate
f :: (
    Defined dom a, Defined AllOf a, Defined cod b, Defined AllOf b
  ) => Fn dom a cod b -> a -> b
f ffn@(Fn fn) x | x ∈ domain ffn = fn x

instance (
    Defined dom a, Defined AllOf a, Defined cod b, Defined AllOf b, Eq b
    ) => Eq (Fn dom a cod b) where
  f1 == f2 = 
    domain f1 === domain f2 && codomain f1 === codomain f2 &&
    (forAll (domain f1) $ \x -> f f1 x == f f2 x)

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
