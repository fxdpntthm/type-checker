module HM.Driver where

{- The main driver file that puts together the compiler transformations -}

import HM.Language
import HM.Util
import HM.Freshen
import HM.AlgorithmW
import HM.AlgorithmM
import Control.Monad.State

runPipelineW :: ExpPs -> Either String Type
runPipelineW e = do (fe, _) <- runStateT (freshen e) initFnS
                    (te, _) <- runStateT (algoW globalCtx fe) initTcS
                    return (fst te)
  
runPipelineM e ty = do (fe, _) <- runStateT (freshen e) initFnS
                       runStateT (algoM globalCtx fe ty) initTcS
