{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Vector (
  Vector,
  (@@),
  cons,
  vecToList,
  reals2, reals3, reals4
) where

import GHC.TypeLits
import Data.Proxy
import Sets

-- To make the vector "well defined" for any n and [a],
-- equality is determined by comparing lists up to n (and padding with 0)
data Vector (n :: Nat) a = Vec (Proxy n) [a]

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

reals2 = Everything :: Set (Vector 2 RealNum)
reals3 = Everything :: Set (Vector 3 RealNum)
reals4 = Everything :: Set (Vector 4 RealNum)
