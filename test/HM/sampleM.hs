module Main where

import HM.Language
import HM.AlgorithmM
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

  putStr $ "+ should succeed:\n\t -- |- \\ x. True <= (a -> Bool)\n\t"
  let v =  runPipelineMCheck (ELam "x" (ELit $ LitB True)) (TArr (TVar "a") (TConst TBool))
  shouldPass v
  
  -- putStr $ "+ should succeed:\n\t -- |- \\ x. True\n\t"
  -- let v =  runPipelineMInfer  (ELam "x" (ELit $ LitB True))
  -- shouldPass v
  
  -- putStr $ "+ should succeed:\n\t |- (\\x. \\y. True)\n\t" 
  -- let v =  runPipelineMInfer (ELam "x" (ELam "y" $ ELit $ LitB True))
  -- shouldPass v

  -- putStr $ "+ should succeed:\n\t |- (\\x.x)\n\t"
  -- let v = runPipelineMInfer (ELam "x" (EVar "x"))
  -- shouldPass v

  -- putStr $ "+ should fail:\n\t |- (\\x.x x)\n\t"
  -- let v = runPipelineMInfer (ELam "x" $ EApp (EVar "x") (EVar "x"))
  -- shouldFail v

  -- putStr $ "+ should succeed:\n\t |- True \n\t"
  -- let v = runPipelineMInfer (ELit $ LitB True)
  -- shouldPass v

  -- putStr $ "+ should succeed:\n\t |- (\\x.x) False\n\t"
  -- let v = runPipelineMInfer (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))
  -- shouldPass v

  putStr $ "+ should succeed:\n\t |- (\\x.x) False <= Bool \n\t"
  let v = runPipelineMCheck (EApp (ELam "x" (EVar "x")) (ELit $ LitB False)) (TConst TBool)
  shouldPass v

  putStr $ "+ should succeed:\n\t -- |- (\\x.x) (\\y.y) <= (a -> a)\n\t"
  let v =  runPipelineMCheck (EApp (ELam "x" (EVar "x")) (ELam "y" (EVar "y"))) (TArr (TVar "a") (TVar "a"))
  shouldPass v

  -- putStr $ "+ should succeed:\n\t -- |- (\\x.x) (\\y.y)\n\t"
  -- let v =  runPipelineMInfer (EApp (ELam "x" (EVar "x")) (ELam "y" (EVar "y")))
  -- shouldPass v

  
  -- putStr $ "+ should fail:\n\t -- |- False (\\x.x)\n\t"
  -- let v =  runPipelineMInfer
  --                    (EApp (ELit $ LitB False)
  --                          (ELam "x" (EVar "x")))
  -- shouldFail v


  -- putStr $ "+ should fail:\n\t -- |- ((\\x.x)(False)) (\\x.x)\n\t"
  -- let v =  runPipelineMInfer
  --                    (EApp (EApp (ELam "x" (EVar "x"))
  --                                (ELit $ LitB False))
  --                          (ELam "x" (EVar "x")))
  -- shouldFail v

  -- putStr $ "+ should succeed:\n\t -- (let id = \\x -> x in (id False))\n\t"
  -- let v =  runPipelineMInfer
  --                    (ELet "id" (ELam "x" (EVar "x"))
  --                      (EApp (EVar "id") (ELit $ LitB False)))
  -- shouldPass v

  -- putStr $ "+ should succeed:\n\t -- letrec f = \\ x -> if x = 0 then 1 else x * (fact x-1) \n\t"
  -- let v =  runPipelineMInfer factExp
  -- shouldPass v

  putStr $ "+ should succeed:\n\t -- letrec f = \\ x -> if x = 0 then 1 else x * (fact x-1) <= Int -> Int\n\t"
  let v =  runPipelineMCheck factExp (TArr (TConst TInt) (TConst TInt))
  shouldPass v

  putStr $ "+ should fail:\n\t -- letrec f = \\ x -> if x = 0 then 1 else x * (fact x=1) <= Int -> Int\n\t"
  let v =  runPipelineMCheck factExpWrong (TArr (TConst TInt) (TConst TInt))
  shouldFail v

  -- putStr $ "+ should succeed:\n\t -- letrec f = \\ x -> if x = 0 then 1 else x * (fact x-1) <= a -> a\n\t"
  -- let v =  runPipelineMCheck factExp (TArr (TVar "a") (TVar "a"))
  -- shouldPass v

  -- putStr $ "+ should succeed:\n\t -- (let id = \\x -> x in (id id))\n\t"
  -- let v =  runPipelineMInfer
  --                    (ELet "id" (ELam "x" (EVar "x"))
  --                      (EApp (EVar "id") (EVar "id")))
  -- shouldPass v


