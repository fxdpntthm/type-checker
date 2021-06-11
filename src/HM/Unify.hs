module HM.Unify where

import HM.Language
import HM.Util
import Control.Monad.State

-- Unify is a function that tries to unify 2 types or returns an error
-- The goal will be to convert left Type into a right Type
-- so that substitute t1 (unify (ty1, ty2)) = ty1{ty1 ~ ty2} = ty2
-- we need to update the state i.e. subs tcm and return a substitution
unify :: Type ->  Type -> TCM Substitution

unify t1@(TArr a b) t2@(TArr c d) = do s <- unify a c
                                       s' <- unify (substitute s b)  (substitute s d)
                                       return $ substitute s' s
                                       
unify (TVar a) x@(TVar b)
  | (a == b) = return eSub
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
