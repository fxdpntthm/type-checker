module Main where

import Language
import AlgorithmW

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
  putStrLn $ show $ unify (TConst TBool) (TConst TBool)
  putStrLn $ show $ unify (TConst TBool) (TArr (TVar "a") (TVar "b"))
  putStrLn $ show $ unify (TVar "a") (TArr (TVar "a") (TVar "b"))
  putStrLn $ show $ unify (TArr (TVar "a") (TVar "b"))
    (TArr (TVar "a") (TVar "b"))
  putStrLn $ show $ unify (TVar "a") (TArr (TVar "b") (TVar "c"))
