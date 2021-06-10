module HM.Driver where

{- The main driver file that puts together the compiler transformations -}

import HM.Language
import HM.Util
import HM.Freshen
import HM.AlgorithmW
import HM.AlgorithmM
import Control.Monad.State

runPipelineW :: ExpPs -> Either String Scheme
runPipelineW e = do (fe, _) <- runStateT (freshen e) initFnS
                    (te, _) <- runStateT (algoW globalCtx fe) initTcS
                    return $ tidyType (fst  te)

runPipelineMCheck :: ExpPs -> Type -> Either String Substitution
runPipelineMCheck e ty = do (fe, _) <- runStateT (freshen e) initFnS
                            (s, _) <- runStateT (algoM globalCtx fe ty) initTcS
                            return s
                            

runPipelineMInfer :: ExpPs -> Either String Scheme
runPipelineMInfer e    = do (fe, _) <- runStateT (freshen e) initFnS
                            let ty = TVar "ty" -- fresh ty
                            (s, _) <- runStateT (algoM globalCtx fe ty) initTcS
                            return $ tidyType (substitute s ty)

