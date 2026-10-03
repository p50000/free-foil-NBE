{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}

-- | lambda-n-ways `nf` / `random15` / `random20` normalisation benchmark,
-- comparing the __real generic free-foil normaliser__ against two
-- hand-written ones.
--
--   * @NBE.FreeFoil (generic)@ — `LambdaPi.nfNbe` from @lambda-pi-demo@, i.e.
--     the actual @Value@/@VSuspended@/@quote@ machinery of
--     @FreeFoil.NbE@ running over the generic free-monad @AST@. The harness'
--     @LC IdInt@ is bridged to the scope-safe @AST@ via the tested
--     @LambdaPi.LambdaNWays@ conversion.
--   * @NBE.FreeFoil (monomorphic)@ — `LambdaPi.Monomorphic.nfMono`: the same
--     algorithm over the same free-foil syntax, but with a hand-written
--     monomorphic value type in place of the generic @Value@. It uses the
--     same conversion as the generic column.
--   * @NBE.Foil@ — the fork's self-contained hand-written foil NbE, which pays
--     for no generic ("free") layer in either its syntax or its values.
--
-- The difference between the generic and the monomorphic column is the cost
-- of the generic value domain; the difference between the monomorphic column
-- and the fork is the cost of free-foil's generic syntax. A correctness check
-- first confirms that each column agrees with the fork (up to alpha) on every
-- term.
--
-- Corpus dir defaults to @../lambda-n-ways-fork/lams/@; override with @LAMS_DIR@.
module Main (main) where

import Control.DeepSeq (force, rnf)
import Control.Monad (forM_)
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
import qualified LambdaPi.Monomorphic as Mono

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

-- | The hand-written monomorphic NbE over the same scope-safe AST as
-- 'genericImpl'. Only @impl_nf@ differs between the two.
monoImpl :: LambdaImpl
monoImpl =
  LambdaImpl
    { impl_name = "NBE.FreeFoil (monomorphic)",
      impl_fromLC = LNW.fromLC . toLNW,
      impl_toLC = fromLNW . LNW.toLC,
      impl_nf = Mono.nfMono emptyScope,
      impl_nfi = error "nfi unimplemented",
      impl_aeq = alphaEquiv emptyScope
    }

impls :: [LambdaImpl]
impls = [genericImpl, monoImpl, Foil.NBE.impl]

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

-- | Does an implementation agree with the fork baseline (up to alpha) on @t@?
agrees :: LambdaImpl -> U.LC U.IdInt -> Bool
agrees impl t =
  case Foil.NBE.impl of
    LambdaImpl{..} ->
      impl_aeq (impl_fromLC (nfLC impl t))
               (impl_fromLC (nfLC Foil.NBE.impl t))

main :: IO ()
main = do
  dir <- fromMaybe "../lambda-n-ways-fork/lams/" <$> lookupEnv "LAMS_DIR"
  lennart <- toIdInt <$> getTerm (dir ++ "lennart.lam")
  random15 <- getTerms (dir ++ "random15.lam")
  random20 <- getTerms (dir ++ "random20.lam")
  let corpus = lennart : random15 ++ random20
  forM_ [genericImpl, monoImpl] $ \impl -> do
    let bad = length (filter (not . agrees impl) corpus)
    putStrLn $ "correctness: " ++ impl_name impl ++ " vs fork baseline on "
      ++ show (length corpus) ++ " terms — "
      ++ (if bad == 0 then "ALL AGREE" else show bad ++ " MISMATCH(ES)")
  defaultMain
    [ bgroup "nf"       [ benchOne  i lennart  | i <- impls ]
    , bgroup "random15" [ benchMany i random15 | i <- impls ]
    , bgroup "random20" [ benchMany i random20 | i <- impls ]
    ]
