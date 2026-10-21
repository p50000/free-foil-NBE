{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Parsing terms of the monolithic language from strings: the
-- BNFC-generated lexer and parser plus free-foil's generated scope
-- resolution. The syntax is that of lambda-pi, pairs and naturals together;
-- a pattern is a name or a pair of names in parentheses, so @split p as
-- (x, y) in t@ and @natrec n { zero -> z ; suc (k, r) -> s }@. The 'IsString'
-- instance parses a closed term; 'parseOpen' takes a scope and an
-- environment for the free variables.
module Monolith.Parser
  ( parseMonolith
  , parseOpen
  , resolve
  , withFreeVars
  ) where

import Data.String (IsString (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.Foil
import Monolith (Monolith)
import Monolith.Generated (toTerm)
import Monolith.Syntax.Abs (Term, VarIdent (..))
import Monolith.Syntax.Par (myLexer, pTerm)

-- | Resolve a raw term into scope-safe syntax; a free variable missing from
-- the environment is an error.
resolve :: Distinct n => Scope n -> Map String (Name n) -> Term -> Monolith n
resolve scope env = toTerm scope (Map.mapKeys VarIdent env)

parseRaw :: String -> Either String Term
parseRaw = pTerm . myLexer

-- | Parse a closed term.
parseMonolith :: String -> Either String (Monolith VoidS)
parseMonolith s = resolve emptyScope Map.empty <$> parseRaw s

-- | Parse a term in a scope, given the names of the variables in it.
parseOpen :: Distinct n => Scope n -> Map String (Name n) -> String -> Either String (Monolith n)
parseOpen scope env s = resolve scope env <$> parseRaw s

instance IsString (Monolith VoidS) where
  fromString = either (error . ("Monolith.Parser: " ++)) id . parseMonolith

-- | Run a continuation in the scope extended with fresh names for the given
-- variables; later names shadow earlier ones.
withFreeVars
  :: Distinct n
  => Scope n
  -> Map String (Name n)
  -> [String]
  -> (forall l. Distinct l => Scope l -> Map String (Name l) -> r)
  -> r
withFreeVars scope env [] k = k scope env
withFreeVars scope env (x : xs) k =
  withFresh scope $ \binder ->
    case assertDistinct binder of
      Distinct ->
        let env' = Map.insert x (nameOf binder) (Map.map sink env)
        in withFreeVars (extendScope binder scope) env' xs k
