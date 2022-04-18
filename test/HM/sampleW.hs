{-# Language ScopedTypeVariables#-}

module Main where

import HM.Language
import HM.AlgorithmW
import HM.Unify
import HM.Util
import HM.Freshen
import Control.Monad.State
import HM.Driver

import Data.Map as Map
import Data.Set as Set
import Data.Either (isRight, isLeft)
import Common


main :: IO ()
main = do
  print (substitute sub1 sub2)
  print (substitute sub1 sub3)

  putStr "+ should succeed: Bool ~ Bool\n\t"
  let v = execStateT (unify (TConst TBool) (TConst TBool)) (TcState mempty 0)
  shouldPass v

  putStr "+ should fail: Bool ~ a -> b\n\t"
  let v = execStateT (unify (TConst TBool) (TArr (TVar "a") (TVar "b"))) (TcState mempty 0)
  shouldFail v

  putStr "+ should fail: a ~ a -> b\n\t"
  let v = execStateT (unify (TVar "a") (TArr (TVar "a") (TVar "b"))) (TcState mempty 0)
  shouldFail v

  putStr "+ should succeed: a -> b ~ a -> b\n\t"
  let v = (execStateT $ unify (TArr (TVar "a") (TVar "b"))
                               (TArr (TVar "a") (TVar "b")))
          (TcState mempty 0)
  shouldPass v

  putStr "+ should succeed: a -> b ~ c -> d\n\t"
  let v = execStateT (unify (TArr (TVar "a") (TVar "b"))
                               (TArr (TVar "c") (TVar "d")))
          (TcState mempty 0)
  shouldPass v

  putStr "+ should succeed: a ~ b -> c \n\t"
  let v = execStateT (unify (TVar "a")
                               (TArr (TVar "b") (TVar "c")))
          (TcState mempty 0)
  shouldPass v

  putStrLn "+ should fail:\n\t -- (y: Bool) |- x"
  let v = (runStateT $ algoW (Context $ Map.singleton (unique 0 "y") (Forall (Set.fromList []) $ TConst TBool))
                      (EVar $ unique 0 "x")) initTcS
  shouldFail v

  putStrLn "+ should succeed:\n\t -- (x: Bool) |- x"
  let v = (runStateT $ algoW (Context $ Map.singleton (unique 0 "x") (Forall (Set.fromList []) $ TConst TBool))
                      (EVar $ unique 0 "x")) initTcS
  shouldPass v

  putStrLn "+ should succeed:\n\t -- () |- \\x. Bool"
  let v = (runStateT $ algoW mempty (ELam (unique 0 "x") (ELit $ LitB True))) initTcS
  shouldPass v

  let e::ExpPs = ELam "x" (ELit $ LitB True)
  putStrLn "+ should succeed:\n\t -- () |- \\x. Bool"
  let v = runPipelineW e
  shouldPass v

  let e::ExpPs = ELam "x" (ELam "y" $ ELit $ LitB True)
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  let v = runPipelineW e
  shouldPass v

  let e::ExpPs = EApp (ELam "x" (EVar "x")) (ELit $ LitB False)
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  let v = runPipelineW e
  shouldPass v

  let e::ExpPs = ELam "x" (EVar "x")
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  let v = runPipelineW e
  shouldPass v

  let e::ExpPs = EApp (ELam "x" (EVar "x")) (ELam "y" (EVar "y"))
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  let v =  runPipelineW e
  shouldPass v

  let e::ExpPs = EApp (ELam "x" (EVar "x")) (ELam "y" (EVar "y")) `EApp` ELit (LitB True)
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  let v =  runPipelineW e
  shouldPass v

  let e::ExpPs = EApp (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))
                                 (ELam "x" (EVar "x"))
  putStrLn $ "+ should fail:\n\t -- () |- " ++ show e
  let v = runPipelineW e
  shouldFail v

  let e::ExpPs = ELet "id" (ELam "x" (EVar "x"))
                            (EApp (EVar "id") (ELit $ LitB False))
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  let v = runPipelineW e
  shouldPass v

  let e::ExpPs = ELet "id" (ELam "x" (EVar "x"))
                         (EApp (EVar "id") (EVar "id"))
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  let v =  runPipelineW e
  shouldPass v

  -- let e::ExpPs = (ELet "id" (ELam "x" (EVar "x")) (EIf (ELit $ LitB True) (ELit $ LitI 1) (EApp (EVar "id") (ELit $ LitI 1))))
  -- putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  -- let v =  runPipelineW e
  -- shouldPass v

  let e::ExpFn = EApp (EVar isZero) (EVar $ mkUnique "n")
  putStrLn $ "+ should succeed:\n\t -- (n:Int) |- " ++ show e
  let v = (runStateT $ algoW (updateContext globalCtx (mkUnique "n") (scheme (TConst TInt))) e) initTcS
  shouldPass v

  let e::ExpPs = ELam "n" (EApp (EVar "isZero") (EVar "n"))
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  let v = runPipelineW e
  shouldPass v

  -- let e::ExpPs = (EIf (ELit $ LitB True) (ELit $ LitI 1) (ELit $ LitB False))
  -- putStrLn $ "+ should fail:\n\t -- () |- " ++ show e
  -- let v =  runPipelineW e
  -- shouldFail v

  putStrLn $ "+ should fail:\n\t -- () |- " ++ show factExpWrong
  let v =  runPipelineW factExpWrong
  shouldFail v

  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show factExp
  let v =  runPipelineW factExp
  shouldPass v


