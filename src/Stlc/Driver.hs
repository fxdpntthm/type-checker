module Stlc.Driver where

{- The main driver file that puts together the compiler transformations -}

import Stlc.Language
import Stlc.Util
import Stlc.Freshen
import Stlc.AlgorithmW
import Control.Monad.State
import Debug.Trace

runPipeline :: ExpPs -> Either String Type
runPipeline e = do (fe, _) <- runStateT (freshen e) initFnS
                   (te, _) <- runStateT (algoW globalCtx fe) initTcS
                   -- traceM $ show fe
                   return (fst te)
  
