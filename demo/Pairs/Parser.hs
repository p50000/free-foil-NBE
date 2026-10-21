{-# LANGUAGE DataKinds         #-}
-- | Parsing pairs terms from strings: the BNFC-generated lexer and parser
-- plus free-foil's generated scope resolution, through "Demo.Parsing". @(a, b)@ is a pair, @fst t@
-- and @snd t@ the projections, @split p as (x, y) in t@ binds both
-- components. The language has no closed terms, so there is no 'IsString'
-- instance: 'parseOpen' takes a scope and an environment for the free
-- variables.
module Pairs.Parser
  ( parseOpen
  , resolve
  , withFreeVars
  ) where

import Data.Map.Strict (Map)

import Control.Monad.Foil
import Demo.Parsing (parseWith, resolveWith, withFreeVars)
import Pairs (Pairs)
import Pairs.Generated (toTerm)
import Pairs.Syntax.Abs (Term, VarIdent (..))
import Pairs.Syntax.Par (myLexer, pTerm)

-- | Resolve a raw term into scope-safe syntax; a free variable missing from
-- the environment is an error.
resolve :: Distinct n => Scope n -> Map String (Name n) -> Term -> Pairs n
resolve = resolveWith toTerm VarIdent

-- | Parse a term in a scope, given the names of the variables in it.
parseOpen :: Distinct n => Scope n -> Map String (Name n) -> String -> Either String (Pairs n)
parseOpen = parseWith (pTerm . myLexer) toTerm VarIdent
