module Stlc.Freshen where

import Stlc.Language
import Stlc.Util
import Control.Monad.State
import Debug.Trace

{- We need to freshen names to makes sure name resolution works fine.
   eg. \x -> let x = 2 in x should freshen to \x_0 -> let x_1 = 2 in x_1
-}

freshen :: ExpPs -> FnM ExpFn
freshen (EVar s) = do i <- get
                      return $ EVar (unique i s)
freshen (ELit l) = return $ ELit l
freshen (ELam x b) = do modify incFnS
                        i <- get
                        b' <- freshen b
                        return $ ELam (unique i x) b'
freshen (EApp e1 e2) = do e1' <- freshen e1
                          e2' <- freshen e2
                          return $ EApp e1' e2'
freshen (ELet x e1 e2) = do modify incFnS
                            i <- get
                            let x' = unique i x
                            e1' <- freshen e1
                            e2' <- freshen e2
                            return $ ELet x' e1' e2'
freshen (EFix x b) = do modify incFnS
                        i <- get
                        b' <- freshen b
                        return $ EFix (unique i x) b'
freshenLit :: Lit -> FnM Lit
freshenLit = return
