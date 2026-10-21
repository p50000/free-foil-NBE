{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- the IsString instance of a synonym over library types
-- | Parsing lambda-pi terms from strings: the BNFC-generated lexer and parser
-- plus free-foil's generated scope resolution, through "Demo.Parsing".
-- Application is juxtaposition, @\\x. t@ is a lambda, @(x : A) -> B@ a
-- dependent function type. The 'IsString' instance parses a closed term;
-- 'parseOpen' takes a scope and an environment for the free variables.
module LambdaPi.Parser
  ( parseLambdaPi
  , parseOpen
  , resolve
  , withFreeVars
  ) where

import Data.String (IsString (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.Foil
import Demo.Parsing (parseWith, resolveWith, withFreeVars)
import LambdaPi (LambdaPi)
import LambdaPi.Generated (toTerm)
import LambdaPi.Syntax.Abs (Term, VarIdent (..))
import LambdaPi.Syntax.Par (myLexer, pTerm)

-- | Resolve a raw term into scope-safe syntax; a free variable missing from
-- the environment is an error.
resolve :: Distinct n => Scope n -> Map String (Name n) -> Term -> LambdaPi n
resolve = resolveWith toTerm VarIdent

-- | Parse a term in a scope, given the names of the variables in it.
parseOpen :: Distinct n => Scope n -> Map String (Name n) -> String -> Either String (LambdaPi n)
parseOpen = parseWith (pTerm . myLexer) toTerm VarIdent

-- | Parse a closed term.
parseLambdaPi :: String -> Either String (LambdaPi VoidS)
parseLambdaPi = parseOpen emptyScope Map.empty

instance IsString (LambdaPi VoidS) where
  fromString = either (error . ("LambdaPi.Parser: " ++)) id . parseLambdaPi
