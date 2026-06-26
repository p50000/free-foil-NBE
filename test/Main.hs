module Main where

import System.Exit (exitFailure)

import LambdaPi

main :: IO ()
main =
  case nfd appTwo of
    Lam _ _ -> putStrLn "lambda-pi NbE: ok"
    _       -> exitFailure
