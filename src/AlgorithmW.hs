{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

module AlgorithmW where

import Language
import Control.Applicative (liftA2)
import Control.Monad (liftM2)
--import Control.Monad.State.Lazy
--import Control.Monad.Except
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Debug.Trace (traceM)

-- Unify is a function that tries to unify 2 types or returns an error
-- The goal will be to convert left Type into a right Type
-- so that substitute t1 (unify (ty1, ty2)) = ty2 if unify returns a Right _
-- we need to update the state i.e. subs tcm and return a ()
unify :: Type ->  Type -> TCM ()
unify (TConst a) (TConst b) | (a == b)  = return ()
                            | otherwise = typeError
                                $ "Cannot unify "
                                  ++ (show a) ++ " and " ++ (show b)
unify (TConst a)  b         = typeError
                             $ "Cannot unify " ++ (show a)
                                ++ " with " ++ show b

unify (TArr a b) (TArr c d) = TCM (\tcs -> do (_, tcs') <- (runTCM $ unify a c) tcs
                                              (_, tcs'') <- (runTCM $ unify b d) tcs'
                                              return ((), tcs'')
                                  )
unify (TVar a) (TVar b)     | (a == b)  = return ()
                            | otherwise = TCM (\tcs ->
                                                 return ((),
                                                         TcState ((subs tcs) `mappend` (sub a (TVar b))) (tno tcs)))

unify (TVar a) x            = do if (a `elem` fvs x)
                                   then typeError
                                              $ "unification will of "
                                              ++ (show a) ++ " and " ++ (show x)
                                              ++ " will lead to infinite type"
                                   else TCM (\tcs ->
                                                 return ((),
                                                         TcState ((subs tcs) `mappend` (sub a x)) (tno tcs)))

unify a b                   = typeError $ "Cannot unify "
                                ++ (show a) ++ " and " ++ (show b)


-- concretizes a scheme to specific type
-- ie. takes all the quantified variables creates new type variables for them
-- and applies all of them to the type
instantiate :: Scheme -> TCM Type
instantiate (Forall q ty) = do q' <- mapM (const $ fresh 't') (Set.toList $ q)
                               let s = Subt (Map.fromList $ zip (Set.toList q) q')
                               return (substitute ty s)

-- TODO
generalize :: Context -> Type -> TCM Scheme
generalize = undefined

-- Typechecker state holds the substitutions that we would have to make
-- in order to typecheck the term and a term number that will be used
-- to create fresh type variables
data TcState = TcState { subs :: Substitution
                       , tno  :: Int } deriving (Show, Eq)

newtype TCM a = TCM { runTCM :: TcState -> Either String (a, TcState) }

gets :: TCM TcState
gets = TCM (\s -> Right (s, s))

-- type TCM a = ExceptT (StateT TcState a)

instance Functor TCM where
  fmap :: (a -> b) -> TCM a -> TCM b
  fmap f tcm = TCM (\s -> do (r, s') <- runTCM tcm s
                             return ((f r), s'))

instance Applicative TCM where
   pure = return
   (<*>) = liftM2 ($)

instance Monad TCM where
    return x = TCM (\s -> Right (x, s))
    TCM sf >>= vf =
        TCM (\s0 -> case sf s0 of
                      Left s -> Left s
                      Right (v, s1) -> runTCM (vf v) s1)

typeError :: String -> TCM a
typeError err = TCM (\_ ->  Left err)

lookupVar :: Context -> Id -> TCM Scheme
lookupVar (Context c) i = case (Map.lookup i c) of
  Just x -> return x
  Nothing -> typeError $ "Variable " ++ i ++ " not in scope"

fresh :: Char -> TCM Type
fresh c = TCM (\tcs -> do let tid = tno tcs
                          return ( TVar (c:'$':(suffixGen !! tid))
                                 , tcs {tno = tid + 1}
                                 )
              )
          where
            suffixGen = liftA2 (\i -> \c -> [c] ++ show i)  [ 0 .. ]  ['a' .. 'z']


-- Algorithm W should assign the most general type for the expression i.e.
-- it should generate a Principal Type Scheme when
-- given a context or should fail with an error
algoW :: Context -> Exp -> TCM (Type, Substitution)
-- algoW = undefined
-- Our Exp can be of 5 types EVar, ELit, ELam, EApp, ELet
-- so we simply patten match on each constructor type and start assigning
-- types

{-
   The first rule is for the literals,
   literals have a constant type. eg. True: Bool 0: Int
   and require no substitution

  -------------------------------------------[Lit]
               Γ ⊢ True : TBool

  -------------------------------------------[Lit]
               Γ ⊢ 3 : TInt

-}

algoW gamma (ELit x) = do case x of
                            LitB _ -> return $ (TConst TBool, mempty)
                            LitI _ -> return $ (TConst TInt, mempty)

{-
   The second rule is for the variable
      x : σ ϵ Γ            τ = instantiate(σ)
   -------------------------------------------[Var]
               Γ ⊢ x : τ

  search if the variable x exists in the context Γ and instantiate it.
  return an error if no such variable exists

-}

algoW gamma (EVar x) = do sig <- lookupVar gamma x              -- x : σ ϵ Γ
                          tau <- instantiate sig                -- τ = inst(σ)
                          return (tau, mempty)                  -- τ

{-
  This rule types lambda expression.
      Γ, x:T ⊢ e :T'
   -------------------------- [Lam]
       Γ ⊢ λx. e : T -> T'

  A new type variable is introduced that is bound to lambda and
  it is added on to the context Γ, the expression is then checked for
  its type and

-}
algoW gamma (ELam x e) = do x' <- fresh 'x'                              -- x:T
                            let gamma' =                                 -- Γ, x:T
                                  updateContext gamma x (scheme x')
                            (ty, s) <- algoW gamma' e                   -- e: T'
                            return (TArr x' ty, s)                      -- T -> T'

{-
   rule for application goes as follows:
   if we have an expression 

      Γ ⊢ e' :T     Γ ⊢ e :T -> T'
   --------------------------------------- [App]
                 Γ ⊢ e e' : T'


-}
algoW gamma (EApp e e') = do (ty, s)  <- algoW gamma e
                             -- traceM ("ty " ++ show ty)
                             (ty', s') <- algoW (substitute gamma s) e'
                             -- traceM ("ty' " ++ show ty')
                             f <- fresh 'f'
                             unify (substitute ty s') (TArr ty' f)
                             s''' <- gets
                             let fs = subs s'''
                             return $ (substitute f fs, fs)
