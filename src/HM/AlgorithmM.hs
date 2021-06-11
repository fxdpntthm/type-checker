{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module HM.AlgorithmM where

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


import HM.Language
import HM.Util

import Control.Monad.State

-- Unify is a function that tries to unify 2 types or returns an error
-- The goal will be to convert left Type into a right Type
-- so that substitute t1 (unify (ty1, ty2)) = ty1{ty1 ~ ty2} = ty2
-- we need to update the state i.e. subs tcm and return a substitution
unify :: Type ->  Type -> TCM Substitution

unify t1@(TArr a b) t2@(TArr c d) = do s <- unify a c
                                       s' <- unify b d
                                       return $ substitute s' s
                                       
unify (TVar a) x@(TVar b)         | (a == b) = return eSub
                                  | otherwise =  do tcs <- get
                                                    let new_s = sub a x
                                                    modify(\tcs -> tcs {subs = substitute (subs tcs) new_s })
                                                    return new_s
unify x1@(TVar a) x
  | (a `elem` fvs x) =  typeError $ infiniteType x1 x
  | otherwise =  do tcs <- get
                    let new_s = sub a x
                    modify(\tcs -> tcs {subs = substitute (subs tcs) new_s })
                    return new_s

unify x x1@(TVar a)
  | (a `elem` fvs x) =  typeError $ infiniteType x1 x
  | otherwise =  do tcs <- get
                    let new_s = sub a x
                    modify(\tcs -> tcs {subs = substitute (subs tcs) new_s })
                    return new_s

unify t1@(TConst a) t2@(TConst b)
  | (a == b)  = return eSub
  | otherwise = typeError $ cannotUnify t1 t2

unify a b                   = typeError $ cannotUnify a b

infiniteType t1 t2 = "unification of "
                     ++ show t1 ++ " and " ++ show t2
                     ++ " will lead to infinite type"
cannotUnify t1 t2 = "Cannot unify " ++ show t1
                    ++ " with " ++ show t2


-- This algorithm takes in the context, expression and
-- the expected type (or type constraint) of the expression and returns the
-- substitution that satisfies the type constraint
-- It is different from algoW:
--    1. it does not return type and substitution.
--    2. It expects a type to be given for which a substitution is returned.
--    3. Unify is called at for Literal, Variable and Lambda (as opposed to Application call in algorithmW)

algoM :: Context -> ExpFn -> Type -> TCM Substitution
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
  LitB _ -> unify expty (TConst TBool) 
  LitI _ -> unify expty (TConst TInt) 

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
                                unify expty tau            -- τ

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
algoM gamma (ELam x e) expty = do b <- fresh 'a'
                                  b' <- fresh 'a'
                                  s <- unify expty (TArr b b')
                                  let gamma' = updateContext (substitute s gamma) x (substitute s  (scheme b))
                                  s' <- algoM gamma' e  (substitute s b')
                                  return $ substitute s' s

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
  type variable as the return type of the second expression (e')
  Then e is checked against type (a -> expty)
  to obtain a substitution for b. Then e' is checked for sanity
-}
algoM gamma (EApp e e') expty = do a <- fresh 'a'
                                   s <- algoM gamma e (TArr a expty)
                                   s' <- algoM (substitute s gamma) e' $ substitute s a
                                   return $ substitute s' s

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
algoM gamma (ELet x e e') expty = do b <- fresh 'b'
                                     s <- algoM gamma e b
                                     sig <- generalize (substitute s gamma) (substitute s b)
                                     let gamma' = updateContext (substitute s gamma) x sig
                                     s' <- algoM gamma' e' (substitute s expty)
                                     return $ substitute s' s

algoM gamma (EIf c e1 e2) expty = do t <- fresh 't'
                                     s <- algoM gamma e1 t
                                     let gamma' = substitute s gamma
                                     s' <- algoM gamma' e2 (substitute s t)
                                     s'' <- algoM gamma' c (TConst TBool)
                                     return $ substitute s'' s'


algoM gamma (EFix f l@(ELam _ _)) expty = do let gamma' = updateContext gamma f (scheme expty)
                                             algoM gamma' l expty

algoM _ e _ = typeError $ "Cannot typecheck current expression: " ++ show e
