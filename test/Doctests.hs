-- | Run the examples in the haddocks of the dependent types demo.
module Main (main) where

import System.Environment (getArgs, unsetEnv)
import Test.DocTest (mainFromLibrary)
import Test.DocTest.Helpers (extractSpecificCabalLibrary, findCabalPackage)

main :: IO ()
main = do
  args <- getArgs
  -- Inside a Nix shell doctest would start GHCi without cabal's package
  -- environment file, and so without the package store. This project is
  -- built by cabal, so the environment file is the right source either way.
  unsetEnv "IN_NIX_SHELL"
  unsetEnv "NIX_BUILD_TOP"
  lib <- extractSpecificCabalLibrary (Just "dependent-types-demo") =<< findCabalPackage "free-foil-nbe"
  mainFromLibrary lib args
