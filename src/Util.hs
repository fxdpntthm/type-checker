module Util where

import Control.Applicative (liftA2)
import Control.Monad.State

-- We need an infinite supply of
-- names for our type variables that we introduce.
suffixGen = liftA2 (\i -> \c -> [c] ++ show i)  [ 0 .. ]  ['a' .. 'z']

