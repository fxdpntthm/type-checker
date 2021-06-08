module Stlc.Freshen where

import Stlc.Language
import Stlc.Util
import Control.Monad.State
import Debug.Trace

{- We need to freshen names to makes sure there is no name shadowing.
   eg. \x -> let x = 2 in x should freshen to \x_0 -> let x_1 = 2 in x_1
   but, letrec f = \x -> f x should freshen to letrec f`0 = \x`1 -> f`0 x`1
-}

freshen :: ExpPs -> FnM ExpFn
freshen (EVar s) = do u <- getUnique s
                      return $ EVar u
freshen (ELit l) = return $ ELit l
freshen (ELam x b) = do modify incFnS
                        x' <- freshUnique x
                        b' <- freshen b
                        return $ ELam  x' b'
freshen (EApp e1 e2) = do e1' <- freshen e1
                          e2' <- freshen e2
                          return $ EApp e1' e2'
freshen (ELet x e1 e2) = do modify incFnS
                            x' <- freshUnique x
                            e1' <- freshen e1
                            e2' <- freshen e2
                            return $ ELet x' e1' e2'
freshen (EIf c t e) = do c' <- freshen c
                         t' <- freshen t
                         e' <- freshen e
                         return $ EIf c' t' e'
freshen (EFix x b) = do modify incFnS
                        x' <- freshUnique x
                        b' <- freshen b
                        return $ EFix x' b'
