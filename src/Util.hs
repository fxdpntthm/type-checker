{-# Language InstanceSigs #-}
module Util where

import Language

import Control.Applicative (liftA2)
import Control.Monad (liftM2)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set, (\\))


-- Convinence function to return an error
typeError :: String -> TCM a
typeError err = TCM (\_ ->  Left err)

-- Looks up a variable and returns the scheme if it exists in the
-- context
lookupVar :: Context -> Id -> TCM Scheme
lookupVar (Context c) i = case (Map.lookup i c) of
  Just x -> return x
  Nothing -> typeError $ "Variable " ++ i ++ " not in context"

-- concretizes a scheme to specific type
-- ie. takes all the quantified variables creates new type variables for them
-- and applies all of them to the type
instantiate :: Scheme -> TCM Type
instantiate (Forall q ty) = do q' <- mapM (const $ fresh 't') (Set.toList $ q)
                               let s = Subt (Map.fromList $ zip (Set.toList q) q')
                               return (substitute ty s)

-- creates a scheme given a context and a type
-- the free variables in the generated scheme
-- are the (free variables in the type) - (free variables in context)
generalize :: Context -> Type -> TCM Scheme
generalize gamma ty = return $ Forall qs ty
  where qs = fvs ty \\ fvs gamma

-- Generate unique type variable for a new term
fresh :: Char -> TCM Type
fresh c = TCM (\tcs -> do let tid = tno tcs
                          return ( TVar (c:'$':(suffixGen !! tid))
                                 , tcs {tno = tid + 1}
                                 )
              )
          where
            suffixGen = liftA2 (\i -> \c -> [c] ++ show i)  [ 0 .. ]  ['a' .. 'z']

-- Typechecker state holds the substitutions that we would use
-- in order to typecheck the term and a term number that will be used
-- to create unique fresh type variables.
data TcState = TcState { subs :: Substitution
                       , tno  :: Int } deriving (Show, Eq)

newtype TCM a = TCM { runTCM :: TcState -> Either String (a, TcState) }

gets :: TCM TcState
gets = TCM (\s -> Right (s, s))

instance Functor TCM where
  fmap :: (a -> b) -> TCM a -> TCM b
  fmap f tcm = TCM (\s -> do (r, s') <- runTCM tcm s
                             return ((f r), s'))

instance Applicative TCM where
   pure = return
   (<*>) = liftM2 ($)

instance Monad TCM where
    return a = TCM (\s -> Right (a, s))
    TCM sf >>= vf =
        TCM (\s0 -> case sf s0 of
                      Left s -> Left s
                      Right (v, s1) -> runTCM (vf v) s1)
