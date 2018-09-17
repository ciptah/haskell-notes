{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Limits
  ( limitFn
  , continuousAt
  )
where

import           Sets
import           Sequences
import           Analysis
import           Vectors
import           Functions

import           Data.Maybe
import           Data.Proxy
import           GHC.TypeLits

-- Proposition 6.3. The limit of a function is unique if it exists
limitFn
  :: (Defined dom (RD n), Defined cod (RD m), KnownNat n, KnownNat m)
  => Fn dom (RD n) cod (RD m)
  -> RD n
  -> Maybe (ExtRD m)
limitFn fn target | accumulation (domain fn) target =
  coalesce
    $ singleton
    $
    -- Apply the function to the approaches, and analyze convergence. Do not
    -- collapse the Maybe because if "Nothing" exists that indicates some path
    -- with undefined convergence, which changes the answer!
      smap lim
    $ smap (extendFn <.)
    $ smap (fn <.)
    $
    -- Only consider approaches within the domain of the function
      collapse
    $ smap (\seq -> box (f seq))
    $
    -- Find all approaches to the target
      approaches
    $ extend
    $ target
 where
  coalesce Nothing  = Nothing
  coalesce (Just x) = x

continuousAt
  :: (KnownNat n, KnownNat m, Defined dom (RD n), Defined cod (RD m))
  => Fn dom (RD n) cod (RD m)
  -> RD n
  -> Bool
continuousAt fn target
  | isolated (domain fn) target
  = True
  | accumulation (domain fn) target
  = limitFn fn target == (Just $ extend $ fn ⬅ target)
