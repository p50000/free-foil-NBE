{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Two views of a lambda-pi value. 'ppValue' quotes it back and prints the
-- term. 'ppValueStruct', also the 'Show' instance, prints its structure:
-- neutral variables, nodes, and each suspended body with its environment.
module LambdaPi.PrettyPrint
  ( ppValue
  , ppValueStruct
  ) where

import Control.Monad.Foil
import Control.Monad.Foil.Internal (Substitution (UnsafeSubstitution))
import Control.Monad.Free.Foil
import qualified Data.IntMap as IntMap
import Data.Void (absurd)
import FreeFoil.NbE (quote)
import qualified FreeFoil.NbE as NbE
import LambdaPi (Value)
import LambdaPi.Generated (TermSig (AppSig, LamSig, PiSig), FFPattern (FFPatternVar), fromTerm)
import LambdaPi.Syntax.Print (printTree)

-- | Quote a value back to a term and print it.
ppValue :: Distinct n => Scope n -> Value n -> String
ppValue scope = printTree . fromTerm . quote scope

-- | Print the structure of a value: @#n@ for a neutral variable, @{node}@ for
-- a node, and @body |env=[...]@ for a suspended body with its environment.
ppValueStruct :: Value n -> String
ppValueStruct = \case
  NbE.VVar x -> '#' : show (nameId x)
  NbE.VNode node ->
    "{" ++ body ++ "}"
    where
      body = case node of
        AppSig f a ->
          "app " ++ ppValueStruct f ++ " " ++ ppValueStruct a
        LamSig sc -> absurd sc
        PiSig _ sc -> absurd sc
  NbE.VSuspended env node ->
    "{" ++ body ++ "}"
    where
      envS = let dom = substitutionDomain env
             in if null dom then "" else " |env=" ++ show dom
      suspended (ScopedAST b t) = binder b ++ ". " ++ show t ++ envS
      body = case node of
        AppSig f a ->
          "app " ++ ppValueStruct f ++ " " ++ ppValueStruct a
        LamSig sc ->
          "lam " ++ suspended sc
        PiSig d sc ->
          "pi " ++ ppValueStruct d ++ " " ++ suspended sc
  where
    binder :: FFPattern i l -> String
    binder (FFPatternVar nb) = 'x' : show (nameId (nameOf nb))

-- | The raw identifiers an environment maps, for display.
substitutionDomain :: Substitution e i o -> [Int]
substitutionDomain (UnsafeSubstitution m) = IntMap.keys m

instance Show (Value n) where
  show = ppValueStruct
