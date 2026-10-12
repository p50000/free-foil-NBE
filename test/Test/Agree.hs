-- | Agreement with a reference normaliser on terms that may diverge.
module Test.Agree (agreesWithin) where

import Control.DeepSeq (NFData, rnf)
import Control.Exception (evaluate)
import Data.Maybe (isJust)
import System.Timeout (timeout)

import Test.Tasty.QuickCheck

-- | Compare a result with the reference result, forcing each under a time
-- budget of one second. The languages are untyped, so a term may diverge. A
-- case is discarded only when the reference diverges too; if the reference
-- finishes and the result does not, the property fails.
agreesWithin :: NFData a => String -> (a -> a -> Bool) -> a -> a -> IO Property
agreesWithin name same reference result = do
  referenceDone <- finished (evaluate (rnf reference))
  resultDone    <- finished (evaluate (rnf result))
  pure $ case (referenceDone, resultDone) of
    (True, True) ->
      counterexample (name ++ " and nfSubst disagree")
        (property (same reference result))
    (False, _) ->
      property Discard
    (True, False) ->
      counterexample
        (name ++ " did not finish within the budget though nfSubst did")
        (property False)
  where
    finished act = isJust <$> timeout budgetMicros act
    budgetMicros = 1000000
