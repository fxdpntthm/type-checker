module Main where

import Language
import AlgorithmM
import Util

import Data.Map as Map
import Data.Set as Set


scheme1 :: Scheme
scheme1 = Forall (Set.fromList ["b"]) (TArr (TVar "a") (TVar "b"))

gamma :: Context
gamma = Context (Map.fromList [ ("add",
                       Forall (Set.fromList ["a"])
                                  (TArr (TArr (TVar "a") (TVar "a")) (TVar "a")))
                              , ("id", Forall (Set.empty)
                                         (TArr (TVar "b") (TVar "b")))
                     ])
sub1 :: Substitution
sub1 = Subt (Map.singleton "a" (TVar "b"))

sub2 :: Substitution
sub2 = Subt (Map.singleton "b" (TVar "c"))



main :: IO ()
main = do
  putStrLn $ show $ substitute sub1 sub2

  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ (unify (TConst TBool) (TConst TBool))) (TcState mempty 0)
  putStr $ "+ should fail:\n\t"
  putStrLn $ show $ (runTCM $ (unify (TConst TBool) (TArr (TVar "a") (TVar "b")))) (TcState mempty 0)
  putStr $ "+ should fail:\n\t"
  putStrLn $ show $ (runTCM $ (unify (TVar "a") (TArr (TVar "a") (TVar "b")))) (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ (unify (TArr (TVar "a") (TVar "b"))
                                     (TArr (TVar "a") (TVar "b"))))
                              (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ (unify (TVar "a")
                                     (TArr (TVar "b") (TVar "c"))))
                            (TcState mempty 0)
  putStr $ "+ should fail:\n\t"
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.singleton "y" (Forall (Set.fromList []) $ TConst TBool)) (EVar "x") (TVar "a"))
                            (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.singleton "x" (Forall (Set.fromList []) $ TConst TBool)) (EVar "x") (TVar "a"))
                            (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty) (ELam "x" (ELit $ LitB True)) (TArr (TVar "a") (TConst TBool)))
                            (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty) (ELam "x" (ELit $ LitB True)) (TVar "a"))
                            (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
                                    (ELam "x" (ELam "y" $ ELit $ LitB True)) (TVar "a"))
                            (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
                     (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))  (TVar "a")
                    ) (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
                     (EApp (ELam "x" (EVar "x")) (ELam "y" (EVar "y")))
                      (TVar "a")
                    ) (TcState mempty 0)
  putStr $ "+ should fail:\n\t"
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
                     (EApp (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))
                           (ELam "x" (EVar "x")))
                       (TConst TBool)
                    ) (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
                     (ELet "id" (ELam "x" (EVar "x"))
                       (EApp (EVar "id") (ELit $ LitB False)))
                       (TVar "a")
                    ) (TcState mempty 0)
