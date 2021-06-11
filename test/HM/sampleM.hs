{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import HM.Language
import HM.AlgorithmM
import HM.Unify
import HM.Util
import HM.Freshen
import HM.Driver

import Data.Map as Map
import Data.Set as Set
import Control.Monad.State
import Debug.Trace
import Common

main :: IO ()
main = do
  putStrLn $ show $ substitute sub1 sub2

  putStr $ "+ should succeed: Bool ~ Bool\n\t"
  let v = (execStateT $ (unify (TConst TBool) (TConst TBool))) (TcState mempty 0)
  shouldPass v

  putStr $ "+ should succeed: a ~ b\n\t"
  let v = (execStateT $ (unify (TVar "a") (TVar "b"))) (TcState mempty 0)
  shouldPass v
  
  putStr $ "+ should fail: Bool ~ a -> b\n\t"
  let v =  (execStateT $ (unify (TConst TBool) (TArr (TVar "a") (TVar "b")))) (TcState mempty 0)
  shouldFail v

  putStr $ "+ should fail: a ~ a -> b\n\t"
  let v =  (execStateT $ (unify (TVar "a") (TArr (TVar "a") (TVar "b")))) (TcState mempty 0)
  shouldFail v
  
  putStr $ "+ should succeed: (a -> b) ~ (a -> b)\n\t"
  let v =  (execStateT $ (unify (TArr (TVar "a") (TVar "b"))
                                     (TArr (TVar "a") (TVar "b"))))
                              (TcState mempty 0)
  shouldPass v

  putStr $ "+ should succeed: (a -> b) ~ (a -> c)\n\t"
  let v =  (execStateT $ (unify (TArr (TVar "a") (TVar "b"))
                                     (TArr (TVar "a") (TVar "c"))))
                              (TcState mempty 0)
  shouldPass v

  putStr $ "+ should succeed: (a -> (b -> c)) ~ (a -> (Bool -> Int))\n\t"
  let v =  (execStateT $ (unify (TArr (TVar "a") (TArr (TVar "b") (TVar "c")))
                                (TArr (TVar "a") (TArr (TConst TBool) (TConst TInt)))))
                              (TcState mempty 0)
  shouldPass v

    
  putStr $ "+ should succeed: (b -> c) ~ a\n\t"
  let v =  (execStateT $ (unify (TArr (TVar "b") (TVar "c"))
                                (TVar "a")))
                            (TcState mempty 0)
  shouldPass v
  
  putStr $ "+ should fail:\n\t -- (y: Bool) |- x\n\t"
  let v =  (execStateT $ algoM (Context $ Map.singleton (mkUnique "y") (Forall (Set.fromList []) $ TConst TBool))
                     (EVar $ mkUnique "x") (TVar "a"))
                            initTcS
  shouldFail v         

  putStr $ "+ should succeed:\n\t -- (x: Bool) |- x \n\t"
  let v =  (execStateT $ algoM (Context $ Map.singleton (mkUnique "x") (Forall (Set.fromList []) $ TConst TBool))
                     (EVar $ mkUnique "x") (TVar "a"))
                            initTcS
  shouldPass v

  let e::ExpPs = (ELam "x" (ELit $ LitB True))
  let ty = (TArr (TVar "a") (TConst TBool))
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e ++ " <= " ++ show ty
  let v =  runPipelineMCheck e ty
  putStr "\t"
  shouldPass v
  
  let e::ExpPs = (ELam "x" (ELit $ LitB True))
  putStrLn $ "+ should succeed:\n\t -- () |- " ++ show e
  let v =  runPipelineMInfer e
  putStr "\t"
  shouldPass v

  let e::ExpPs = (ELam "x" (ELam "y" $ ELit $ LitB True))
  putStrLn $ "+ should succeed:\n\t |- (\\x. \\y. True)" 
  let v =  runPipelineMInfer e
  putStr "\t"
  shouldPass v

  let e::ExpPs = (ELam "x" (EVar "x"))
  putStrLn $ "+ should succeed: |- " ++ show e
  let v = runPipelineMInfer e
  putStr "\t"
  shouldPass v

  let e::ExpPs = (ELam "x" $ EApp (EVar "x") (EVar "x"))
  putStrLn $ "+ should fail: () |- " ++  show e
  let v = runPipelineMInfer e
  putStr "\t"
  shouldFail v

  let e::ExpPs =(ELit $ LitB True)
  putStrLn $ "+ should succeed: |- " ++ show e
  let v = runPipelineMInfer e
  putStr "\t"
  shouldPass v

  let e::ExpPs = (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))
  putStrLn $ "+ should succeed: |- " ++ show e
  let v = runPipelineMInfer e
  putStr "\t"
  shouldPass v

  let e::ExpPs = (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))
  let ty = (TConst TBool)
  putStrLn $ "+ should succeed: |- " ++ show e ++ " <= " ++ show ty
  let v = runPipelineMCheck e ty
  putStr "\t"
  shouldPass v

  let e::ExpPs = (EApp (ELam "x" (EVar "x")) (ELam "y" (EVar "y")))
  let ty = (TArr (TVar "a") (TVar "a"))
  putStrLn $ "+ should succeed: -- () |- " ++ show e ++ " <= " ++ show ty
  let v =  runPipelineMCheck e ty
  putStr "\t"
  shouldPass v

  let e::ExpPs = (EApp (ELam "x" (EVar "x")) (ELam "y" (EVar "y")))
  putStrLn $ "+ should succeed: -- () |- " ++ show e
  let v =  runPipelineMInfer e
  putStr "\t"
  shouldPass v

  let e::ExpPs = (EApp (ELit $ LitB False)
                           (ELam "x" (EVar "x")))
  putStrLn $ "+ should fail: -- () |- " ++ show e
  let v =  runPipelineMInfer e
  putStr "\t"
  shouldFail v

  let e::ExpPs = (EApp (EApp (ELam "x" (EVar "x"))
                         (ELit $ LitB False))
                   (ELam "x" (EVar "x")))
  putStrLn $ "+ should fail: -- () |- " ++ show e
  let v =  runPipelineMInfer e
  putStr "\t"
  shouldFail v

  let e::ExpPs = (ELet "id" (ELam "x" (EVar "x"))
                       (EApp (EVar "id") (ELit $ LitB False)))
  putStrLn $ "+ should succeed: -- () |- " ++ show e
  let v =  runPipelineMInfer e
  putStr "\t"
  shouldPass v

  putStrLn $ "+ should succeed: -- () |- " ++ show factExp
  let v =  runPipelineMInfer factExp
  putStr "\t"
  shouldPass v

  let ty = (TArr (TConst TInt) (TConst TInt))
  putStrLn $ "+ should succeed: -- () |- " ++ show factExp ++ " <= " ++ show ty
  let v =  runPipelineMCheck factExp ty
  putStr "\t"
  shouldPass v


  let ty = (TArr (TConst TInt) (TConst TInt))
  putStrLn $ "+ should fail: -- () |- " ++ show factExpWrong ++ " <= " ++ show ty
  let v =  runPipelineMCheck factExpWrong ty
  putStr "\t"
  shouldFail v

  let ty = (TArr (TVar "a") (TVar "a"))
  putStrLn $ "+ should succeed: -- () |- " ++ show factExp ++ " <= " ++ show ty
  let v =  runPipelineMCheck factExp ty
  putStr "\t"
  shouldPass v

  let e::ExpPs = (ELet "id" (ELam "x" (EVar "x"))
                       (EApp (EVar "id") (EVar "id")))
  putStrLn $ "+ should succeed: -- () |- " ++ show e
  let v =  runPipelineMInfer e
  putStr "\t"
  shouldPass v


