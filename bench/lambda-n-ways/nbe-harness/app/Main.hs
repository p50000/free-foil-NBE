{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}

-- | lambda-n-ways `nf` / `random15` / `random20` normalisation benchmark,
-- comparing the __real generic free-foil normaliser__ against the fork's
-- hand-written foil NbE.
--
--   * @NBE.FreeFoil (generic)@ — `LambdaPi.nfNbe` from @lambda-pi-demo@, i.e.
--     the actual @Value@/@ScopedClosure@/@quote@ machinery of
--     @FreeFoil.NbE@ running over the generic free-monad @AST@. The harness'
--     @LC IdInt@ is bridged to the scope-safe @AST@ via the tested
--     @LambdaPi.LambdaNWays@ conversion.
--   * @NBE.Foil@ — the fork's self-contained hand-written foil NbE, which pays
--     for no generic ("free") layer.
--
-- The difference between the two columns is the cost of that layer. A
-- correctness check first confirms the two agree (up to alpha) on every term.
--
-- Corpus dir defaults to @../lambda-n-ways-fork/lams/@; override with @LAMS_DIR@.
module Main (main) where

import Control.DeepSeq (force, rnf)
import Data.Maybe (fromMaybe)
import System.Environment (lookupEnv)
import Test.Tasty.Bench

import qualified Util.IdInt as U
import qualified Util.Syntax.Lambda as U
import Util.Impl (LambdaImpl (..), getTerm, getTerms, toIdInt)
import qualified Foil.NBE

import FreeFoil.NbE (alphaEquiv, emptyScope)
import qualified LambdaPi as LP
import qualified LambdaPi.LambdaNWays as LNW

-- Bridge the harness' own LC/IdInt to the mirrored ones in LambdaPi.LambdaNWays,
-- whose fromLC/toLC build/read the real scope-safe AST. (Structural identity.)
toLNW :: U.LC U.IdInt -> LNW.LC LNW.IdInt
toLNW = \case
  U.Var (U.IdInt i)   -> LNW.Var (LNW.IdInt i)
  U.Lam (U.IdInt i) b -> LNW.Lam (LNW.IdInt i) (toLNW b)
  U.App f a           -> LNW.App (toLNW f) (toLNW a)

fromLNW :: LNW.LC LNW.IdInt -> U.LC U.IdInt
fromLNW = \case
  LNW.Var (LNW.IdInt i)   -> U.Var (U.IdInt i)
  LNW.Lam (LNW.IdInt i) b -> U.Lam (U.IdInt i) (fromLNW b)
  LNW.App f a             -> U.App (fromLNW f) (fromLNW a)

-- | The generic free-foil NbE as a harness `LambdaImpl`. Internal type is the
-- real scope-safe AST (@LambdaPi VoidS@); @impl_nf@ is the real generic
-- @nfNbe@, so this measures the free-monad layer, not a re-implementation.
-- @impl_fromLC@/@impl_toLC@ (the conversion) run outside the timed @impl_nf@,
-- matching how @Foil.NBE@ is measured.
genericImpl :: LambdaImpl
genericImpl =
  LambdaImpl
    { impl_name = "NBE.FreeFoil (generic)",
      impl_fromLC = LNW.fromLC . toLNW,
      impl_toLC = fromLNW . LNW.toLC,
      impl_nf = LP.nfNbe emptyScope,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = alphaEquiv emptyScope
    }

impls :: [LambdaImpl]
impls = [genericImpl, Foil.NBE.impl]

benchOne :: LambdaImpl -> U.LC U.IdInt -> Benchmark
benchOne LambdaImpl{..} lc =
  let !tm = force (impl_fromLC lc)
   in bench impl_name (nf (rnf . impl_nf) tm)

benchMany :: LambdaImpl -> [U.LC U.IdInt] -> Benchmark
benchMany LambdaImpl{..} lcs =
  let !tms = force (map impl_fromLC lcs)
   in bench impl_name (nf (rnf . map impl_nf) tms)

-- | Normal form of a term as a named 'LC', via a given implementation.
nfLC :: LambdaImpl -> U.LC U.IdInt -> U.LC U.IdInt
nfLC LambdaImpl{..} = impl_toLC . impl_nf . impl_fromLC

-- | Does the generic NbE agree with the fork baseline (up to alpha) on @t@?
agrees :: U.LC U.IdInt -> Bool
agrees t =
  case Foil.NBE.impl of
    LambdaImpl{..} ->
      impl_aeq (impl_fromLC (nfLC genericImpl t))
               (impl_fromLC (nfLC Foil.NBE.impl t))

main :: IO ()
main = do
  dir <- fromMaybe "../lambda-n-ways-fork/lams/" <$> lookupEnv "LAMS_DIR"
  lennart <- toIdInt <$> getTerm (dir ++ "lennart.lam")
  random15 <- getTerms (dir ++ "random15.lam")
  random20 <- getTerms (dir ++ "random20.lam")
  let corpus = lennart : random15 ++ random20
      bad = length (filter (not . agrees) corpus)
  putStrLn $ "correctness: generic free-foil NbE vs fork baseline on "
    ++ show (length corpus) ++ " terms — "
    ++ (if bad == 0 then "ALL AGREE" else show bad ++ " MISMATCH(ES)")
  defaultMain
    [ bgroup "nf"       [ benchOne  i lennart  | i <- impls ]
    , bgroup "random15" [ benchMany i random15 | i <- impls ]
    , bgroup "random20" [ benchMany i random20 | i <- impls ]
    ]
