{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}

-- | Minimal reproduction of the lambda-n-ways @nf@ / @random15@ / @random20@
-- normalisation benchmarks, restricted to the NbE-on-foil implementations we
-- care about: the fork's closure NbE ("Foil.NBE", baseline) and the
-- free-foil-NBE eager-values port ("Foil.EagerNBE", this work).
--
-- Uses the fork's real corpus (@lams/*.lam@) and real conversion/parsing
-- (@Util.Impl.getTerm@ / @getTerms@ / @toIdInt@), but is compiled with a modern
-- GHC (native aarch64) since the fork's GHC 8.10.7 cannot build on Apple
-- Silicon. Before the benchmark it cross-checks that the port's normal forms
-- are alpha-equal to the baseline's on every corpus term.
--
-- The corpus directory defaults to @../lams/@ (this project living inside the
-- fork clone); override with the @LAMS_DIR@ environment variable.
module Main (main) where

import Control.DeepSeq (force, rnf)
import System.Environment (lookupEnv)
import Test.Tasty.Bench

import Util.IdInt (IdInt)
import Util.Syntax.Lambda (LC)
import Util.Impl (LambdaImpl (..), getTerm, getTerms, toIdInt)

import qualified Foil.NBE
import qualified Foil.EagerNBE

impls :: [LambdaImpl]
impls =
  [ Foil.EagerNBE.impl  -- free-foil-NBE eager-values port (this work)
  , Foil.NBE.impl       -- fork's closure NbE over foil (baseline)
  ]

-- | Normalise one term and force the result.
benchOne :: LambdaImpl -> LC IdInt -> Benchmark
benchOne LambdaImpl{..} lc =
  let !tm = force (impl_fromLC lc)
   in bench impl_name (nf (rnf . impl_nf) tm)

-- | Normalise a whole list of terms and force the results.
benchMany :: LambdaImpl -> [LC IdInt] -> Benchmark
benchMany LambdaImpl{..} lcs =
  let !tms = force (map impl_fromLC lcs)
   in bench impl_name (nf (rnf . map impl_nf) tms)

-- | Normal form of a term as a named 'LC', via a given implementation.
nfLC :: LambdaImpl -> LC IdInt -> LC IdInt
nfLC LambdaImpl{..} = impl_toLC . impl_nf . impl_fromLC

-- | Does the eager-values port agree with the baseline (up to alpha) on @t@?
agreesWithBaseline :: LC IdInt -> Bool
agreesWithBaseline t =
  case Foil.NBE.impl of
    LambdaImpl{..} ->
      impl_aeq (impl_fromLC (nfLC Foil.EagerNBE.impl t))
               (impl_fromLC (nfLC Foil.NBE.impl t))

main :: IO ()
main = do
  dir <- maybe "../lams/" id <$> lookupEnv "LAMS_DIR"
  lennart <- toIdInt <$> getTerm (dir ++ "lennart.lam")
  random15 <- getTerms (dir ++ "random15.lam")
  random20 <- getTerms (dir ++ "random20.lam")
  let corpus = lennart : random15 ++ random20
      bad = length (filter (not . agreesWithBaseline) corpus)
  putStrLn $ "correctness: eager-values port vs baseline on "
    ++ show (length corpus) ++ " terms — "
    ++ (if bad == 0 then "ALL AGREE" else show bad ++ " MISMATCH(ES)")
  defaultMain
    [ bgroup "nf"       [ benchOne  i lennart  | i <- impls ]
    , bgroup "random15" [ benchMany i random15 | i <- impls ]
    , bgroup "random20" [ benchMany i random20 | i <- impls ]
    ]
