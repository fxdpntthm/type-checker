module Stlc.Driver where

{- The main driver file that puts together the compiler transformations -}

import Stlc.Language
import Stlc.Util
import Stlc.Freshen
import Stlc.AlgorithmW
import Stlc.AlgorithmM
import Control.Monad.State
import Debug.Trace

runPipelineW :: ExpPs -> Either String Type
runPipelineW e = do (fe, _) <- runStateT (freshen e) initFnS
                    (te, _) <- runStateT (algoW globalCtx fe) initTcS
                    -- traceM $ show fe
                    return (fst te)
  
runPipelineM e ty= do (fe, _) <- runStateT (freshen e) initFnS
                      runStateT (algoM globalCtx fe ty) initTcS
