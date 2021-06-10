module Common where

import HM.Language
import HM.AlgorithmW
import HM.Util
import HM.Freshen
import Control.Monad.State
import HM.Driver

import Data.Map as Map
import Data.Set as Set
import Data.Either (isRight, isLeft)

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
                     
factExp :: ExpPs
factExp = EFix "fact" (ELam "n" (EIf (EApp (EVar "isZero") (EVar "n"))
                                     (ELit $ LitI 1)
                                     (EApp (EApp (EVar "mult") (EVar "n")) (EApp (EVar "fact") (EApp (EVar "dec") (EVar "n"))))))


assert :: Bool -> IO ()
assert b = if b then return () else error "assertion failed"

shouldPass, shouldFail :: Show a => Either String a -> IO ()
shouldPass exp = do putStrLn $ show exp
                    assert (isRight exp)

shouldFail exp = do putStrLn $ show exp
                    assert (isLeft exp)
