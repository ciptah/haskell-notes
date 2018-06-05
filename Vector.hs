{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Vector (
  Vector,
  Selection,
  (@@), (!>),
  sel, project,
  cons,
  vecToList,
  vmap,
  reals2, reals3, reals4
) where

import GHC.TypeLits
import Data.Proxy
import Sets

-- To make the vector "well defined" for any n and [a],
-- equality is determined by comparing lists up to n (and padding with 0)
data Vector (n :: Nat) a = Vec (Proxy n) [a]

-- Select m unique things from 0..n-1
data Selection (m :: Nat) (n :: Nat) = Select (Vector m Integer)

-- Zero-based dimension.
(@@) :: (KnownNat n, Num a) => Vector n a -> Int -> a
(Vec p x) @@ d | (fromInteger $ natVal p) > d =
  if d >= length x then 0 else x !! d
               | otherwise = error "out of range!"

cons :: a -> Vector n a -> Vector (n + 1) a
cons v (Vec _ x) = Vec Proxy (v:x)

vecToList :: (KnownNat n, Num a) => Vector n a -> [a]
vecToList v@(Vec p x) = map (v @@) [0..((fromInteger $ natVal p) - 1)]

instance (KnownNat n, Eq a, Num a) => Eq (Vector n a) where
  vx@(Vec p x) == vy
    | natVal p == 0 = True
    | otherwise = vecToList vx == vecToList vy

instance (KnownNat n, Eq a, Num a, Show a) => Show (Vector n a) where
  show v = show $ vecToList v

(!>) :: Vector n a -> Selection m n -> Vector m a
(!>) = error "TODO"

sel :: [Int] -> Selection m n
sel = error "TODO"

-- pick several components of the vector.
project :: (Eq a, Num a) =>
  Set (Vector n a) -> Selection m n -> Set (Vector m a)
--project vs selection = smap (\v -> v !> selection) vs
project = error " Blah!" -- Needs KnownNat

-- Apply a function to every component.
vmap :: (Eq a, Num a, KnownNat n) => (a -> b) -> Vector n a -> Vector n b
vmap fn v = Vec Proxy $ map fn $ vecToList v

reals2 = Everything :: Set (Vector 2 RealNum)
reals3 = Everything :: Set (Vector 3 RealNum)
reals4 = Everything :: Set (Vector 4 RealNum)
