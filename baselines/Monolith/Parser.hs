{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- the IsString instance of a synonym over library types
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
import Demo.Parsing (parseWith, resolveWith, withFreeVars)
import Monolith (Monolith)
import Monolith.Generated (toTerm)
import Monolith.Syntax.Abs (Term, VarIdent (..))
import Monolith.Syntax.Par (myLexer, pTerm)

-- | Resolve a raw term into scope-safe syntax; a free variable missing from
-- the environment is an error.
resolve :: Distinct n => Scope n -> Map String (Name n) -> Term -> Monolith n
resolve = resolveWith toTerm VarIdent

-- | Parse a term in a scope, given the names of the variables in it.
parseOpen :: Distinct n => Scope n -> Map String (Name n) -> String -> Either String (Monolith n)
parseOpen = parseWith (pTerm . myLexer) toTerm VarIdent

-- | Parse a closed term.
parseMonolith :: String -> Either String (Monolith VoidS)
parseMonolith = parseOpen emptyScope Map.empty

instance IsString (Monolith VoidS) where
  fromString = either (error . ("Monolith.Parser: " ++)) id . parseMonolith
