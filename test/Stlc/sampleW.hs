{-# Language ScopedTypeVariables#-}

module Main where

import Stlc.Language
import Stlc.AlgorithmW
import Stlc.Util
import Stlc.Freshen
import Control.Monad.State
import Stlc.Driver

import Data.Map as Map
import Data.Set as Set
import Data.Either (isRight, isLeft)
import Common


main :: IO ()
main = do
  putStrLn $ show $ substitute sub1 sub2

  putStr $ "+ should succeed: Bool ~ Bool\n\t"
  let v = (execStateT $ (unify (TConst TBool) (TConst TBool))) (TcState mempty 0)
  shouldPass v
  
  putStr $ "+ should fail: Bool ~ a -> b\n\t"
  let v = (execStateT $ (unify (TConst TBool) (TArr (TVar "a") (TVar "b")))) (TcState mempty 0)
  shouldFail v

  putStr $ "+ should fail: a ~ a -> b\n\t"
  let v = (execStateT $ (unify (TVar "a") (TArr (TVar "a") (TVar "b")))) (TcState mempty 0)
  shouldFail v
  
  putStr $ "+ should succeed: a -> b ~ a -> b\n\t"
  let v = (execStateT $ (unify (TArr (TVar "a") (TVar "b"))
                               (TArr (TVar "a") (TVar "b"))))
          (TcState mempty 0)
  shouldPass v
  
  putStr $ "+ should succeed: a ~ b -> c \n\t"
  let v = (execStateT $ (unify (TVar "a")
                               (TArr (TVar "b") (TVar "c"))))
          (TcState mempty 0)
  shouldPass v
  
  putStrLn $ "+ should fail:\n\t -- (y: Bool) |- x"
  let v = (execStateT $ algoW (Context $ Map.singleton (unique 0 "y") (Forall (Set.fromList []) $ TConst TBool))
                      (EVar $ unique 0 "x")) initTcS
  shouldFail v
  
  putStrLn $ "+ should succeed:\n\t -- (x: Bool) |- x"
  let v = (execStateT $ algoW (Context $ Map.singleton (unique 0 "x") (Forall (Set.fromList []) $ TConst TBool))
                      (EVar $ unique 0 "x")) initTcS
  shouldPass v
  
  putStrLn $ "+ should succeed:\n\t -- () |- \\x. Bool"
  let v = (execStateT $ algoW mempty (ELam (unique 0 "x") (ELit $ LitB True))) initTcS
  shouldPass v
  
  putStrLn $ "+ should succeed:\n\t -- () |- \\x. \\y. True"
  let v = runPipelineW (ELam "x" (ELam "y" $ ELit $ LitB True))
  shouldPass v
  
  putStrLn $ "+ should succeed:\n\t -- () |- (\\x. x) (False)"
  let v = runPipelineW (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))
  shouldPass v
  
  putStrLn $ "+ should succeed:\n\t -- () |- (\\x. x)"
  let v = runPipelineW (ELam "x" (EVar "x"))
  shouldPass v
  
  putStrLn $ "+ should succeed:\n\t -- () |- (\\x. x) (\\y. y)"
  let v =  runPipelineW (EApp (ELam "x" (EVar "x")) (ELam "y" (EVar "y")))
  shouldPass v
  
  putStrLn $ "+ should fail:\n\t -- () |- ((\\x. x) (False))(\\x.x)"
  let v = runPipelineW (EApp (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))
                                 (ELam "x" (EVar "x")))
  shouldFail v
    
  putStrLn $ "+ should succeed:\n\t -- () |- let id = \\x.x in (id False)"
  let v = runPipelineW (ELet "id" (ELam "x" (EVar "x"))
                                 (EApp (EVar "id") (ELit $ LitB False)))
  shouldPass v
  
  putStrLn $ "+ should succeed:\n\t -- (id: \\/ a. a -> a) |- Fix id \\x. id True"
  let v = runPipelineW factExp
  shouldPass v
