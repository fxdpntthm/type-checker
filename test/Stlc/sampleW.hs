module Main where

import Stlc.Language
import Stlc.AlgorithmW
import Stlc.Util
import Stlc.Freshen
import Control.Monad.State
import Stlc.Driver

import Data.Map as Map
import Data.Set as Set


scheme1 :: Scheme
scheme1 = Forall (Set.fromList ["b"]) (TArr (TVar "a") (TVar "b"))

gamma :: Context
gamma = Context (Map.fromList [ (unique 0 "add",
                       Forall (Set.fromList ["a"])
                                  (TArr (TArr (TVar "a") (TVar "a")) (TVar "a")))
                              , (unique 0 "id", Forall (Set.empty)
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
  putStrLn $ show $ (execStateT $ (unify (TConst TBool) (TConst TBool))) (TcState mempty 0)
  putStr $ "+ should fail:\n\t"
  putStrLn $ show $ (execStateT $ (unify (TConst TBool) (TArr (TVar "a") (TVar "b")))) (TcState mempty 0)
  putStr $ "+ should fail:\n\t"
  putStrLn $ show $ (execStateT $ (unify (TVar "a") (TArr (TVar "a") (TVar "b")))) (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (execStateT $ (unify (TArr (TVar "a") (TVar "b"))
                                     (TArr (TVar "a") (TVar "b"))))
                              (TcState mempty 0)
  putStr $ "+ should succeed:\n\t"
  putStrLn $ show $ (execStateT $ (unify (TVar "a")
                                     (TArr (TVar "b") (TVar "c"))))
                            (TcState mempty 0)
  putStrLn $ "+ should fail:\n\t -- (y: Bool) |- x"
  putStrLn $ show $ (execStateT $ algoW (Context $ Map.singleton (unique 0 "y") (Forall (Set.fromList []) $ TConst TBool))
                      (EVar $ unique 0 "x")) initTcS
  putStrLn $ "+ should succeed:\n\t -- (x: Bool) |- x"
  putStrLn $ show $ (execStateT $ algoW (Context $ Map.singleton (unique 0 "x") (Forall (Set.fromList []) $ TConst TBool))
                      (EVar $ unique 0 "x")) initTcS
  putStrLn $ "+ should succeed:\n\t -- () |- \\x. Bool"
  putStrLn $ show $ (execStateT $ algoW mempty (ELam (unique 0 "x") (ELit $ LitB True))) initTcS
  putStrLn $ "+ should succeed:\n\t -- () |- \\x. \\y. True"
  putStrLn $ show $ (do (fe, _) <- (runStateT (freshen (ELam "x" (ELam "y" $ ELit $ LitB True)))) initFnS
                        (te, _) <- (runStateT $ algoW mempty fe) initTcS
                        return $ fst te)
  putStrLn $ "+ should succeed:\n\t -- () |- (\\x. x) (False)"
  putStrLn $ show $ runPipeline (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))

  putStrLn $ "+ should succeed:\n\t -- () |- (\\x. x)"
  putStrLn $ show $ runPipeline (ELam "x" (EVar "x"))

  putStrLn $ "+ should succeed:\n\t -- () |- (\\x. x) (\\y. y)"
  putStrLn $ show $ runPipeline (EApp (ELam "x" (EVar "x")) (ELam "y" (EVar "y")))

  putStrLn $ "+ should fail:\n\t -- () |- ((\\x. x) (False))(\\x.x)"
  putStrLn $ show $ runPipeline (EApp (EApp (ELam "x" (EVar "x")) (ELit $ LitB False))
                                 (ELam "x" (EVar "x")))
    
  putStrLn $ "+ should succeed:\n\t -- () |- let id = \\x.x in (id False)"
  putStrLn $ show $ runPipeline (ELet "id" (ELam "x" (EVar "x"))
                                 (EApp (EVar "id") (ELit $ LitB False)))

  putStrLn $ "+ should succeed:\n\t -- (id: \\/ a. a -> a) |- Fix id \\x. id True"
  putStrLn $ show $ runPipeline factExp


factExp :: ExpPs
factExp = EFix "fact" (ELam "n" (EIf (EApp (EVar "isZero") (EVar "n"))
                                     (ELit $ LitI 1)
                                     (EApp (EApp (EVar "mult") (EVar "n")) (EApp (EVar "fact") (EApp (EVar "dec") (EVar "n"))))))
