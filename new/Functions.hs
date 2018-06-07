{-# LANGUAGE DataKinds #-}

module Functions(
) where

import Sets

data Fn domain a codomain b = Fn (a -> b) (domain a) (codomain b)

exec :: Fn d a c b -> a -> b
exec (Fn fn _ _) x = fn x

type RealFn = Fn AllOf RealNum AllOf RealNum
type TimeFn = Fn Positive RealNum AllOf RealNum
