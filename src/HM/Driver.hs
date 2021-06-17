module HM.Driver where

{- The main driver file that puts together the compiler transformations -}

import HM.Language
import HM.Util
import HM.Freshen
import HM.AlgorithmW
import HM.AlgorithmM
import Control.Monad.State

runPipelineW :: ExpPs -> Either String Scheme
runPipelineW e = do (te , _ ) <- (runFreshen >=> runAlgoW) e
                    return $ tidyType (fst  te)

runFreshen e = runStateT (freshen e) initFnS
runAlgoW (e,_) = runStateT (algoW globalCtx e) initTcS
                      

runPipelineMInfer :: ExpPs -> Either String Scheme
runPipelineMInfer e    = do (s, _) <- (runFreshen >=> runAlgoMInfer) e
                            return $ tidyType (substitute s (TVar "ty"))

runAlgoMInfer (e, _) = runStateT (algoM globalCtx e (TVar "ty")) initTcS

runPipelineMCheck :: ExpPs -> Type -> Either String Scheme
runPipelineMCheck e ty = do (fe, _) <- runStateT (freshen e) initFnS
                            (s, _) <- runStateT (algoM globalCtx fe ty) initTcS
                            return $ tidyType (substitute s ty)
