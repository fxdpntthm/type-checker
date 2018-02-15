module AlgorithmW where

import Language

-- Unify is a function that tries to unify 2 types or returns an error
-- The goal will be to convert left Type into a right Type
-- so that substitute t1 (unify (ty1, ty2)) = ty2 if unify returns a Right _

unify :: Type ->  Type -> Either UnifyError Substitution

unify (TConst a) (TConst b) | (a == b)  = Right (mempty)
                            | otherwise = Left (
                                UnificationFailed
                                $ "Cannot unify "
                                  ++ (show a) ++ " and " ++ (show b))
unify (TConst a)  b         = Left (UnificationFailed
                             $ "Cannot unify " ++ (show a)
                                ++ " with " ++ show b)

unify (TArr a b) (TArr c d) = do sub1 <- unify a c
                                 let n = substitute (b, d) sub1
                                 sub2 <- unify (fst n) (snd n)
                                 return (sub1 `mappend` sub2)

unify (TVar a) (TVar b)     | (a == b)  = Right (mempty)
                            | otherwise = Right (sub a (TVar b))

unify (TVar a) x            = do if (a `elem` fvs x)
                                   then Left (UnificationFailed
                                              $ "unification will of "
                                              ++ (show a) ++ " and " ++ (show x)
                                              ++ " will lead to infinite type")
                                   else Right (sub a x)

unify a b                   = Left (UnificationFailed $ "Cannot unify "
                                    ++ (show a) ++ " and " ++ (show b))

-- Algorithm W should assign the most general type for the expression i.e.
-- it should generate a Principal Type Scheme when
-- given a context or should fail with an error
algoW :: Context -> Exp -> Either String (Type, Substitution)
algoW = undefined
-- Our Exp can be of 5 types EVar, ELit, ELam, EApp, ELet
-- so we simply patten match on each constructor type and start assigning
-- types


{-
   The first rule is for the variable or [Var]
      x belongs to G
   ------------------ [Var]
       G |- x: Type

-}

{-
   The second rule is for the literals, it is similar to Var
   but literals will have a constant type. eg. True: Bool 0: Int
      x belongs to G
   ------------------ [Lit]
       G |- x: Type

-}

{-
  This rule types the abstraction or lambda expression.
      G, x:T |- e :T'
   -------------------------- [Lit]
       G |- \x. e: T -> T'
-}

