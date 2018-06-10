{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}

module Vectors (
  Zero(zero),
  Vector(Vec),
  dim,
  (@@),
  vecToList,
  vzip, vmap, (|+|), (|-|), (|*), (*|),
  norm1, norm2, normInf, perpendicular,
  Selection,
  sel, selFn, pickFn,
  (!>),
  project,
  zeroV,

  R1, R2, RD, UnitBall, Direction, OpenBall(..)
) where

import GHC.TypeLits
import Data.Proxy
import Data.Maybe (fromJust)

import Sets
import Functions

-------------- Basics ------------------

-- Things with a "Zero" element.
class (Eq x, Num x, Ord x) => Zero x where zero :: x

instance Zero RealNum where zero = 0.0
instance Zero Integer where zero = 0

-- To make the vector "well defined" for any n and [a],
-- equality is determined by comparing lists up to n (and padding with 0)
data Vector (n :: Nat) a = Vec [a]

dim_ :: (KnownNat n) => Proxy n -> Vector n a -> Integer
dim_ proxy vec = natVal proxy

-- Dimensions of the vector.
dim :: (KnownNat n) => Vector n a -> Integer
dim vec = dim_ Proxy vec

-- Element access operator.
(@@) :: (KnownNat n, Zero a) => Vector n a -> Integer -> a
v@(Vec lst) @@ d | dim v > d =
  if d >= fromIntegral (length lst) then zero else lst !! (fromIntegral d)

-- Converting to list, length is always of dimension.
vecToList :: (Zero a, KnownNat n) => Vector n a -> [a]
vecToList v@(Vec x) = map (v @@) [0..((fromIntegral $ dim v) - 1)]

-------------- Instantiations ------------------

instance (KnownNat n, Zero a) => Eq (Vector n a) where
  vx == vy
    | dim vx == 0 = True
    | otherwise = vecToList vx == vecToList vy

instance (KnownNat n, Zero a, Show a) => Show (Vector n a) where
  show v = show $ vecToList v

-- All vector elements must be valid instances of a (relative to AllOf a).
instance (KnownNat n, Zero a, Defined AllOf a) => Defined AllOf (Vector n a)
  where candidate _ x = and $ map valid $ vecToList x

instance (Zero a, Ord a) => Ord (Vector 1 a)
  where v1 <= v2 = v1 @@ 0 <= v2 @@ 0

-------------- Vector ops ------------------

-- Apply a function to every component.
vmap :: (Zero a, KnownNat n) => (a -> b) -> Vector n a -> Vector n b
vmap fn v = Vec $ map fn $ vecToList v

vzip :: (Zero a, Zero b, Zero c, KnownNat n)
  => (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
vzip fn v1 v2 =
  Vec $ map (\(x, y) -> fn x y) $ zip (vecToList v1) (vecToList v2)

infixl 6 |+|
(|+|) :: (Zero a, KnownNat n) => Vector n a -> Vector n a -> Vector n a
v1 |+| v2 = vzip (+) v1 v2

infixl 6 |-|
(|-|) :: (Zero a, KnownNat n) => Vector n a -> Vector n a -> Vector n a
v1 |-| v2 = vzip (-) v1 v2

infixl 7 *|
(*|) :: (Zero a, KnownNat n) => a -> Vector n a -> Vector n a
w *| v2 = vmap (w *) v2

infixl 7 |*
(|*) :: (Zero a, KnownNat n) => Vector n a -> a -> Vector n a
v2 |* w = vmap (w *) v2

infixl 7 |.| -- dot product
(|.|) :: (Zero a, KnownNat n) => Vector n a -> Vector n a -> a
v1 |.| v2 = sum $ vecToList $ vzip (*) v1 v2

norm1 :: (Zero a, KnownNat n) => Vector n a -> a
norm1 v = sum $ vecToList $ vmap abs v

norm2 :: (KnownNat n) => Vector n RealNum -> RealNum
norm2 v = sqrt $ v |.| v

normInf :: (Zero a, KnownNat n) => Vector n a -> a
normInf v = maximum $ vecToList $ vmap abs v

perpendicular :: (KnownNat n) => Vector n RealNum -> Vector n RealNum -> Bool
perpendicular v1 v2 = v1 |.| v2 == 0

distance :: (KnownNat n) => Vector n RealNum -> Vector n RealNum -> RealNum
distance v1 v2 = norm2 $ v1 |-| v2

-------------- Selection/projection ------------------

-- Select m unique things from 0..n-1
data Selection (m :: Nat) (n :: Nat) = Select (Vector m Integer)

validSel_ :: (KnownNat m, KnownNat n) =>
  Selection m n -> Proxy m -> Proxy n -> Bool
validSel_ (Select v) pm pn = and $ map (\x -> x < natVal pn) $ vecToList v

-- All vector elements must be valid instances of a (relative to AllOf a).
instance (KnownNat m, KnownNat n) => Defined AllOf (Selection m n)
  where candidate _ sel = validSel_ sel Proxy Proxy

sel_ :: (KnownNat m, KnownNat n) =>
  Proxy m -> Proxy n -> [Integer] -> Maybe (Selection m n)
sel_ pm pn lst = let c = Select $ Vec lst in
  if validSel_ c pm pn then Just c else Nothing

sel :: (KnownNat m, KnownNat n) => [Integer] -> Maybe (Selection m n)
sel lst = sel_ Proxy Proxy lst

-- Pick several components of the vector.
(!>) :: (Zero a, KnownNat m, KnownNat n)
  => Vector n a -> Selection m n -> Vector m a
vec !> (Select sel) = vmap (vec @@) sel

-- Project all the vectors in the set.
project
  :: (Zero a, Defined set (Vector n a), Defined AllOf a,
      KnownNat m, KnownNat n) =>
     set (Vector n a) -> Selection m n -> Subset (Vector m a)
project vs selection = smap (\v -> v !> selection) vs

selFn :: (KnownNat n, KnownNat m, Zero a,
          Defined set (Vector n a),
          Defined set (Vector m a))
  => Selection m n -> Fn set (Vector n a) set (Vector m a)
selFn sel = fromJust $ box $ (!> sel)

-- The "set" constraint isn't propagated form the vector to the contents.
pickFn :: (KnownNat n, Zero a,
          Defined set (Vector n a),
          Defined AllOf a)
  => Integer -> Fn set (Vector n a) AllOf a
pickFn d = fromJust $ box $ (@@ d)

zeroV :: (KnownNat n) => Vector n RealNum
zeroV = Vec []

-------------- Examples ---------------------

-- Sets of vectors in N dimensions.
type R1 = Vector 1 RealNum
type R2 = Vector 2 RealNum
type RD n = Vector n RealNum

type UnitBall = Set "UnitBall"
type Direction = Set "Direction"

-- Open balls are important for neighborhoods, and open sets.
data OpenBall v = OpenBall {
  center :: v,
  radius :: RealNum
}

data Segment v = Segment {
  pointA :: v,
  pointB :: v
}

instance (KnownNat n) => Defined UnitBall (RD n) where
  candidate _ v = norm2 v <= 1.0
instance (KnownNat n) => Defined Direction (RD n) where
  candidate _ v = norm2 v == 1.0

-- Open balls of a certain radius centered around a point.
instance (KnownNat n) => Defined OpenBall (RD n) where
  candidate (OpenBall c rad) v = distance c v < rad
instance (KnownNat n) => Defined AllOf (OpenBall (RD n)) where
  candidate _ (OpenBall c rad) = valid c && valid rad && rad >= 0

-- Nontrivial line segment between two points.
instance (KnownNat n) => Defined Segment (RD n) where
  candidate (Segment pA pB) x = thereExists (Everything :: ZeroOne RealNum) $
    \d -> x == pA |+| d *| (pB |-| pA)
instance (KnownNat n) => Defined AllOf (Segment (RD n)) where
  candidate _ (Segment pA pB) = valid pA && valid pB && pA /= pB
   

