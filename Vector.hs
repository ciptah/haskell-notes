{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Vector (
) where

import GHC.TypeLits
import Data.Proxy
import Sets

data Vector (n :: Nat) a = Vec (Proxy n) [a]

instance (Eq a) => Eq (Vector n a) where
  (Vec _ x) == (Vec _ y) = x == y

z = Vec (Proxy :: Proxy 3) [3, 5]
t = Vec (Proxy :: Proxy 3) [3, 7]
j = Vec (Proxy :: Proxy 4) [3, 7]
