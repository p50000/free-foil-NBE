{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- the IsString instance of a synonym over library types
-- | Parsing naturals terms from strings: the BNFC-generated lexer and parser
-- plus free-foil's generated scope resolution, through "Demo.Parsing". @zero@ and @suc t@ are the
-- numerals, @natrec n { zero -> z ; suc k, r -> s }@ is primitive recursion.
-- The 'IsString' instance parses a closed term; 'parseOpen' takes a scope
-- and an environment for the free variables.
module Naturals.Parser
  ( parseNaturals
  , parseOpen
  , resolve
  , withFreeVars
  ) where

import Data.String (IsString (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.Foil
import Demo.Parsing (parseWith, resolveWith, withFreeVars)
import Naturals (Naturals)
import Naturals.Generated (toTerm)
import Naturals.Syntax.Abs (Term, VarIdent (..))
import Naturals.Syntax.Par (myLexer, pTerm)

-- | Resolve a raw term into scope-safe syntax; a free variable missing from
-- the environment is an error.
resolve :: Distinct n => Scope n -> Map String (Name n) -> Term -> Naturals n
resolve = resolveWith toTerm VarIdent

-- | Parse a term in a scope, given the names of the variables in it.
parseOpen :: Distinct n => Scope n -> Map String (Name n) -> String -> Either String (Naturals n)
parseOpen = parseWith (pTerm . myLexer) toTerm VarIdent

-- | Parse a closed term.
parseNaturals :: String -> Either String (Naturals VoidS)
parseNaturals = parseOpen emptyScope Map.empty

instance IsString (Naturals VoidS) where
  fromString = either (error . ("Naturals.Parser: " ++)) id . parseNaturals
