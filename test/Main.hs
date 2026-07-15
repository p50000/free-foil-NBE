module Main where

import System.Exit (exitFailure)

import LambdaPi

main :: IO ()
main = do
  case nfd appTwo of
    Lam _ _ -> putStrLn "lambda-pi nf: ok"
    _       -> exitFailure
  if neutralNbeOk
    then putStrLn "lambda-pi NbE (neutral): ok"
    else exitFailure
