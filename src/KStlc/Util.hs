{-# Language InstanceSigs #-}
module KStlc.Util where

import KStlc.LanguageK

import Control.Applicative (liftA2)
import Control.Monad (liftM2)
import Control.Monad.State

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set, (\\))


-- Convinence function to return an error
typeError :: String -> TCM a
typeError err = StateT (\_ ->  Left err)

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
                               let s = Subt (Map.fromList $ zip (Set.toList q) q'
                                            , Map.empty) -- pull out kinds for type variables from the context
                               return (s # ty)

-- creates a scheme given a context and a type
-- the free variables in the generated scheme
-- are the (free variables in the type) - (free variables in context)
generalize :: Context -> Type -> TCM Scheme
generalize gamma ty = return $ Forall qs ty
  where qs = fvs ty \\ fvs gamma

-- Generate unique type variable for a new term
fresh :: Char -> TCM Type
fresh c = StateT (\(TcState s i k) -> return (TVar (KVar ("k`" ++ (suffixGen !! k))) (c:'`':(suffixGen !! i))
                                             , TcState s (i + 1) (k+1)))
  where
    suffixGen = liftA2 (\i -> \pre -> [pre] ++ show i)  [ (1::Integer) .. ]  ['a' .. 'z']
    
-- Typechecker state holds the substitutions that we would use
-- in order to typecheck the term and a term number that will be used
-- to create unique fresh type variables.
data TcState = TcState { subs :: Substitution
                       , tno  :: Int
                       , kno  :: Int } deriving (Show, Eq)

modifySubstitution :: Substitution
                   -> (Map Id Type -> Map Id Type)
                   -> (Map Id Kind -> Map Id Kind)
                   -> Substitution
modifySubstitution (Subt m) f g = Subt (f (fst m), g (snd m))  

type TCM a = StateT TcState  (Either String) a
