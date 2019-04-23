module Main where

import Stlc.Language
import Stlc.AlgorithmM
import Stlc.Util
-- import Stlc.Printer

import Data.Map as Map
import Data.Set as Set


scheme1 :: Scheme
scheme1 = Forall (Set.fromList ["b"]) (TArrSp (TVar "a") (TVar "b"))

gamma :: Context
gamma = Context (Map.fromList [ ("add",
                                  (Forall (Set.fromList ["a"])
                                     (TArrSp (TArrSp (TVar "a") (TVar "a")) (TVar "a")), Set.empty))
                              , ("id", (Forall (Set.empty)
                                       (TArrSp (TVar "b") (TVar "b")), Set.empty))
                              ])
sub1 :: Substitution
sub1 = Subt (Map.singleton "a" (TVar "b"))

sub2 :: Substitution
sub2 = Subt (Map.singleton "b" (TVar "c"))

-- separating pair
spPair = ELamSp "x" (ELamSp "y" (ELamSp "f" (EApp (EVar "f") (EApp (EVar "x") (EVar "y")))))

-- sharing pair
shPair  = ELamSp "x" (ELamSh "y" (ELamSh "f" (EApp (EApp (EVar "f") (EVar "x")) (EVar "y"))))
shPType = TArrSp (TVar "a")
                 (TArrSh (TVar "a'")
                         (TArrSh (TArrSh (TVar "a") (TArrSh (TVar "a'") (TVar "v")))
                                 (TVar "v")))

main :: IO ()
main = do
  putStrLn $ ppr $ substitute sub1 sub2
  putStrLn $ "Separating Pair:\n\t\t" ++ (ppr spPair)
  putStrLn $ "Sharing Pair:\n\t\t" ++ (ppr shPair)
  putStrLn $ "Sharing Pair Type:\n\t\t" ++ (ppr shPType) 

  -- putStr $ "+ should succeed:\n\t"
  -- putStrLn $ show $ (runTCM $ (unify (TConst TBool) (TConst TBool))) (TcState mempty 0 Set.empty)

  -- putStr $ "+ should fail:\n\t"
  -- putStrLn $ show $ (runTCM $ (unify (TConst TBool) (TArrSp (TVar "a") (TVar "b")))) (TcState mempty 0 Set.empty)

  -- putStr $ "+ should fail:\n\t"
  -- putStrLn $ show $ (runTCM $ (unify (TVar "a") (TArrSp (TVar "a") (TVar "b")))) (TcState mempty 0 Set.empty)

  -- putStr $ "+ should succeed:\n\t"
  -- putStrLn $ show $ (runTCM $ (unify (TArrSp (TVar "a") (TVar "b"))
  --                                    (TArrSp (TVar "a") (TVar "b"))))
  --                             (TcState mempty 0 Set.empty)

  -- putStr $ "+ should succeed:\n\t"
  -- putStrLn $ show $ (runTCM $ (unify (TVar "a")
  --                                    (TArrSp (TVar "b") (TVar "c"))))
  --                           (TcState mempty 0 Set.empty)
  putStrLn $ "+ Should succeed:"
  putStrLn $ "\t |- " ++ ppr ((ELit $ LitB False))
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
                      (ELit $ LitB False)
                     (TVar "a")
                    ) (TcState mempty 0 Set.empty)

  putStrLn $ "+ Should succeed:"
  putStrLn $ "\t |- " ++ ppr ((ELit $ LitI 3))
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
                      (ELit $ LitI 3)
                     (TVar "a")
                    ) (TcState mempty 0 Set.empty)

  -- putStr $ "+ Should succeed:\n"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
  --                    (EApp (ELamSp "x" (EVar "x"))
  --                                (ELit $ LitB False)
  --                    )
  --                   (TVar "a")
  --                   ) (TcState mempty 0 Set.empty)
  -- putStr $ "+ should fail:\n\t"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.singleton "y" (Forall (Set.fromList []) $ TConst TBool, Set.empty)) (EVar "x") (TVar "a"))
  --                           (TcState mempty 0 Set.empty)

  -- putStr $ "+ should succeed:\n\t"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.singleton "x" ((Forall (Set.fromList []) (TConst TBool)), Set.empty)) (EVar "x") (TVar "a"))
  --                           (TcState mempty 0 Set.empty)

  -- putStr $ "+ should succeed:\n\t"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty) (ELamSp "x" (ELit $ LitB True)) (TArrSp (TVar "a") (TConst TBool)))
  --                           (TcState mempty 0 Set.empty)

  -- putStr $ "+ should succeed:\n\t"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty) (ELamSp "x" (ELit $ LitB True)) (TVar "a"))
  --                           (TcState mempty 0 Set.empty)


  -- putStr $ "+ should succeed:\n"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
  --                                   (ELamSp "x" (ELamSp "y" $ ELit $ LitB True)) (TVar "a"))
  --                           (TcState mempty 0 Set.empty)

  -- putStr $ "+ should succeed:\n"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
  --                    (EApp (ELamSp "x" (EVar "x")) (ELit $ LitB False))  (TConst TBool)
  --                   ) (TcState mempty 0 Set.empty)

  -- putStr $ "+ should succeed:\n"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
  --                    (EApp (ELamSp "x" (EVar "x")) (ELamSp "y" (EVar "y")))
  --                     (TArrSp (TVar "a") (TVar "a"))
  --                   ) (TcState mempty 0 Set.empty)

  -- putStr $ "+ should fail:\n"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
  --                    (EApp (ELit $ LitB False)
  --                      (ELamSp "y" (EVar "y")))
  --                    (TVar "a")
  --                   ) (TcState mempty 0 Set.empty)
  -- putStr $ "+ Should fail:\n"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
  --                    (EApp (EApp (ELamSp "x" (EVar "x"))
  --                                (ELit $ LitB False)
  --                          )
  --                          (ELamSp "y" (EVar "y"))
  --                    )
  --                   (TVar "a")
  --                   ) (TcState mempty 0 Set.empty)

  putStrLn "+ Should succeed:"
  putStrLn $ "\t |- " ++ ppr shPair
  putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty) shPair shPType)
    (TcState mempty 0 Set.empty)


  -- putStr $ "+ should succeed:\n\t"
  -- putStrLn $ show $ (runTCM $ algoM (Context $ Map.empty)
  --                    (ELet "id" (ELamSp "x" (EVar "x"))
  --                      (EApp (EVar "id") (ELit $ LitB False)))
  --                      (TVar "a")
  --                   ) (TcState mempty 0)
