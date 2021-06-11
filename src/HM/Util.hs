{-# Language InstanceSigs #-}
module HM.Util where

import HM.Language

import Control.Applicative (liftA2)
import Control.Monad (liftM2)
import Control.Monad.State
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set, (\\))
import qualified Data.Hashable as H (hash)

------------------------
-- Freshening Utils  ---
------------------------

data FnState = FnS {
    seed :: Int                -- threaded state seed
  , table :: Map String Unique -- maps current variables to their uniques
                   }
  deriving (Show)
               
incFnS :: FnState -> FnState
incFnS (FnS {seed = s, table = t }) = FnS {seed = s + 1, table=t}

type FnM a = StateT FnState (Either String) a

-- Generates a unique given a string
unique :: Int -> String -> Unique
unique s n = Unique { value = n, hash = H.hash n, scope = s}

-- Generates a fresh unique to be used in this scope
-- Overwrites the existing if it already existed in the table
freshUnique :: String -> FnM Unique
freshUnique n = do (FnS {table = t, seed = s}) <- get
                   let u = unique s n
                   let s' = FnS {table = Map.insert n u t, seed = s+1}
                   put s'
                   return u

-- Gets the unique for the given name that is in this scope
-- If there is none in scope, it creates one
getUnique :: String -> FnM Unique
getUnique n = do s <- get
                 case Map.lookup n (table s) of
                   Nothing -> freshUnique n
                   Just u -> return u

mkUnique = unique 0

isZero = mkUnique "isZero"
mult = mkUnique "mult"
minus = mkUnique "-"
eq = mkUnique "="

globals :: [Unique]
globals = [ isZero, mult, minus, eq]

initFnS = FnS {seed = 0, table = Map.fromList (fmap (\u -> (value u, u)) globals)}

-------------------------
-- Type checking Utils --
-------------------------
-- empty substitution
eSub :: Substitution
eSub = Subt Map.empty

-- empty substitution
eCtx :: Context
eCtx = Context Map.empty

-- Convinence function to return an error
typeError :: String -> TCM a
typeError err = StateT (\_ ->  Left err)

-- Looks up a variable and returns the scheme if it exists in the
-- context
lookupVar :: Context -> Unique -> TCM Scheme
lookupVar (Context c) i = case (Map.lookup i c) of
  Just x -> return x
  Nothing -> typeError $ "Variable " ++ show i ++ " not in context"

-- concretizes a scheme to specific type
-- ie. takes all the quantified variables creates new type variables for them
-- and applies all of them to the type
instantiate :: Scheme -> TCM Type
instantiate (Forall qs ty) = do fqs <- mapM (const $ fresh 't') qs'
                                let s = Subt (Map.fromList $ zip qs' fqs)
                                return (substitute s ty)
                                  where qs' = Set.toList qs

-- creates a scheme given a context and a type
-- the free variables in the generated scheme
-- are the (free variables in the type) - (free variables in context)
generalize :: Context -> Type -> TCM Scheme
generalize gamma ty = return $ generalize' gamma ty

generalize' :: Context -> Type -> Scheme
generalize' gamma ty = Forall qs ty
  where qs = fvs ty \\ fvs gamma


-- Generate unique type variable for a new term
fresh :: Char -> TCM Type
fresh c = do tcs <- get
             modify incTno
             return $ TVar (c:'`': (suffixGen !! (tno tcs)))
  where
    suffixGen = liftA2 (\i -> \pre -> [pre] ++ show i)  [ (1::Int) .. ]  ['a' .. 'z']

incTno :: TcState -> TcState
incTno (TcState {subs = s, tno = t}) = TcState {subs = s, tno = t + 1}

initTcS = TcState { subs = mempty, tno = 0 }


globalCtx = Context $ Map.fromList [ (isZero, scheme (TArr (TConst TInt) (TConst TBool)))
                                   , (mult, scheme (TArr (TConst TInt) (TArr (TConst TInt) (TConst TInt))))
                                   , (minus, scheme (TArr (TConst TInt) (TArr (TConst TInt) (TConst TInt))))
                                   , (eq, Forall (Set.fromList ["a"]) ((TVar "a") `TArr` ((TVar "a") `TArr` (TConst TBool))))]

-- after the inference is done, we get a type, but we'd like to generalize that to a scheme
tidyType :: Type -> Scheme
tidyType = generalize' eCtx 

-- Typechecker state holds the substitutions that we would use
-- in order to typecheck the term and a term number that will be used
-- to create unique fresh type variables.
data TcState = TcState { subs :: Substitution
                       , tno  :: Int } deriving (Show, Eq)

type TCM a = StateT TcState  (Either String) a
