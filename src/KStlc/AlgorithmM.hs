{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module KStlc.AlgorithmM where

-- This is a context-sensitive top-down approach to type checking
-- The pros are that:
--     1. It terminates much earlier than AlgorithmW if the term is illtyped
--     2. error messages are more legible and can pin point the "real" problem
--        in the expression
-- The cons are:
--     1. We would need give a top level binding for the expression that
--        sources to be the expected type of of the expression
--        (or just give a TVar type and unify will take care of it)
-- References:
--     1. Proofs about a folklore let-polymorphic type inference algorithm
--        https://dl.acm.org/citation.cfm?id=291892


import Language
import Util


import qualified Data.Map as Map
import Data.Map (Map)

import Control.Monad (liftM2)


-- Unify is a function that tries to unify 2 types or returns an error
-- The goal will be to convert left Type into a right Type
-- so that substitute t1 (unify (ty1, ty2)) = ty2 if unify returns a Right _
-- we need to update the state i.e. subs tcm and return a ()
unify :: Type ->  Type -> TCM Substitution
unify t1@(TArr a b) t2@(TArr c d) = TCM (\tcs -> do -- traceM ("DEBUG (unify t1 t2)\n\t" ++ show t1 ++ "\n\t" ++ show t2)
                                                    (_, tcs') <- (runTCM $ unify a c) tcs
                                                    -- traceM ("DEBUG (unify a c): " ++  show tcs')
                                                    let s = subs tcs'
                                                    (_, tcs'') <- (runTCM $ unify (substitute b s) (substitute d s)) tcs'
                                                    -- traceM ("DEBUG (unify b d): " ++  show tcs'')
                                                    return (subs tcs'', tcs'')
                                        )
unify (TVar a) x@(TVar b)         | (a == b) = return (Subt Map.empty)
                                  | otherwise =  TCM (\tcs ->
                                                        return ((subs tcs) `mappend` (sub a x)
                                                               ,tcs {subs = (subs tcs) `mappend` (sub a x)}))
unify (TVar a) x          = do if (a `elem` fvs x)
                               then typeError
                                    $ "unification of "
                                    ++ (show a) ++ " and " ++ (show x)
                                    ++ " will lead to infinite type"
                               else TCM (\tcs ->
                                            return ((subs tcs) `mappend` (sub a x)
                                                   , tcs { subs = (subs tcs) `mappend` (sub a x)}))
unify x (TVar a)          = do if (a `elem` fvs x)
                               then typeError
                                    $ "unification of "
                                    ++ (show a) ++ " and " ++ (show x)
                                    ++ " will lead to infinite type"
                               else TCM (\tcs ->
                                            return ((subs tcs) `mappend` (sub a x)
                                                   , tcs { subs = (subs tcs) `mappend` (sub a x)}))
unify (TConst a) (TConst b) | (a == b)  = return (Subt Map.empty)
                            | otherwise = typeError
                                $ "Cannot unify "
                                  ++ (show a) ++ " and " ++ (show b)
unify (TConst a)  b         = typeError
                             $ "Cannot unify " ++ (show a)
                                ++ " with " ++ show b

unify a b                   = typeError $ "Cannot unify "
                                ++ (show a) ++ " and " ++ (show b)

-- This algorithm takes in the context, expression and
-- the expected type (or type constraint) of the expression and returns the
-- substitution that satisfies the type constraint
-- It is different from algoW:
--    1. it does not return type and substitution.
--    2. It expects a type to be given for which a substitution is returned.
--    3. Unify is called at for Literal, Variable and Lambda (as opposed to Application call in algorithmW)

algoM :: Context -> Exp -> Type -> TCM Substitution
-- patten match on all the expression constructs


{-
   The first rule is for the literals,
   literals have a constant type. eg. True: Bool 0: Int
   and require no substitution

  -------------------------------------------[Lit]
               Γ ⊢ True : TBool

  -------------------------------------------[Lit]
               Γ ⊢ 3 : TInt

  unify is called here so as to fix the type of the literal
-}
algoM gamma (ELit x) expty = case x of
  LitB _ -> unify (TConst TBool) expty
  LitI _ -> unify (TConst TInt) expty

{-
   The second rule is for the variable
      x : σ ϵ Γ            τ = instantiate(σ)
   -------------------------------------------[Var]
               Γ ⊢ x : τ

  search if the variable x exists in the context Γ and instantiate it.
  returns a unification of expected type and instantiated type
  or an error if no such variable exists.

-}
algoM gamma (EVar x) expty = do sig <- lookupVar gamma x   -- x : σ ϵ Γ
                                tau <- instantiate sig     -- τ = inst(σ)
                                unify tau expty            -- τ

{-
  This rule types lambda expression.
          Γ, x:T ⊢ e :T'
   -------------------------- [Lam]
       Γ ⊢ λx. e : T -> T'

  2 new fresh type variables are introduced, for x and e. They are unifed with
  the expected type. The new type variable for x is used to extend the context
  and the expression e is checked to return the final substition
  with extended context with substituions applied.

-}
algoM gamma (ELam x e) expty = do b1 <- fresh 'x'
                                  b2 <- fresh 'e'
                                  s  <- unify (TArr b1 b2) expty
                                  let gamma' = updateContext gamma x (scheme b1)
                                  s' <- algoM (substitute gamma' s) e (substitute b2 s)
                                  return (substitute s s')

{-
   rule for application goes as follows:
   if we have an expression e e'
   then if the second expression e is well typed to T
   and the first expression should be of the form T -> T'
   then complete expression is of type T'


      Γ ⊢ e : T -> T'    Γ ⊢ e' :T
   --------------------------------------- [App]
                 Γ ⊢ e e' : T'


  The interesting bit here is we have to introduce a new
  type variable as the return type of the first expression.
  Then e is checked against the TArr b expected type
  to obtain a substitution for b. Then e' is checked for sanity
-}
algoM gamma (EApp e e') expty = do b <- fresh 'e'
                                   s <- algoM gamma e (TArr b expty)
                                   let gamma' = substitute gamma s
                                   let b' = substitute b s
                                   s' <- algoM gamma' e' b'
                                   return (substitute s s')

{-
    Let bindings introduce variable names and associated types
    into the context Γ.

    The procedure for this rule is:
    Obtain the type of e and bind it to x
    then type check e' with the updated context

       Γ ⊢ e : T    sig = gen(Γ,T)    Γ, x: sig ⊢ e' :T'
   -------------------------------------------------------- [Let]
                  Γ ⊢ let x = e in e' : T'

-}
algoM gamma (ELet x e e') expty = do b <- fresh 'e'
                                     s <- algoM gamma e b
                                     sig <- generalize gamma (substitute b s)
                                     let gamma' = updateContext gamma x sig
                                     s' <- algoM (substitute gamma' s) e' (substitute expty s)
                                     return (substitute s s')

algoM gamma (EFix f'@(EVar f) l@(ELam x e)) expty = do b <- fresh 'f'
                                                       let gamma' = updateContext gamma f (scheme b)
                                                       algoM gamma' l expty

algoM _ _ _ = typeError "Cannot typecheck current expression"
