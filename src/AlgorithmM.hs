{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module AlgorithmM where

import Language
import Control.Monad (liftM2)

-- The Type checker state that contains
-- substitution and integer
data TcState = TcState { subs :: Substitution
                       , tno :: Int}

-- The Type checker monad that threads the TcState around
newtype TCM a = TCM {runTCM :: TcState -> Either String (a, TcState) }
  deriving (Functor)


instance Applicative TCM where
  pure a = TCM (\tcs -> Right (a, tcs))
  (<*>)  = liftM2 ($)

instance Monad TCM where
  return a = TCM (\tcs -> Right (a, tcs))
  TCM sf >>= vf =
        TCM (\s0 -> case sf s0 of
                      Left s -> Left s
                      Right (v, s1) -> runTCM (vf v) s1)

algoM :: Context -> Exp -> TCM (Type, Substitution)
algoM = undefined
