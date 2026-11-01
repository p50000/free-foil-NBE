{-# LANGUAGE DataKinds #-}
-- | Parsing dependent pairs terms from strings: the BNFC-generated lexer and
-- parser plus free-foil's generated scope resolution, through
-- "Demo.Parsing". @\\(x : A). t@ is a lambda, @(x : A) -> B@ a function type,
-- @(x : A) * B@ a pair type, @(a, b)@ a pair,
-- @split p : (x : A) * B as (x, y) in t@ takes a pair apart, @U@ is the
-- universe, @Unit@ the unit type and @tt@ its value. The terms are raw:
-- "DependentPairs.Elaborate" elaborates them.
module DependentPairs.Parser
  ( parseOpen
  , resolve
  , withFreeVars
  ) where

import Data.Map.Strict (Map)

import Control.Monad.Foil
import Demo.Parsing (parseWith, resolveWith, withFreeVars)
import DependentPairs (Raw)
import DependentPairs.Generated (toTerm)
import DependentPairs.Syntax.Abs (Term, VarIdent (..))
import DependentPairs.Syntax.Par (myLexer, pTerm)

-- | Resolve a raw term into scope-safe syntax; a free variable missing from
-- the environment is an error.
resolve :: Distinct n => Scope n -> Map String (Name n) -> Term -> Raw n
resolve = resolveWith toTerm VarIdent

-- | Parse a term in a scope, given the names of the variables in it.
parseOpen :: Distinct n => Scope n -> Map String (Name n) -> String -> Either String (Raw n)
parseOpen = parseWith (pTerm . myLexer) toTerm VarIdent
