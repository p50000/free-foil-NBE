{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- the IsString instance of a synonym over library types
-- | Parsing lambda-let terms from strings: the BNFC-generated lexer and
-- parser plus free-foil's generated scope resolution, through "Demo.Parsing". Application is
-- juxtaposition, @\\x. t@ is a lambda, @let x = e in t@ a let whose body
-- extends as far right as possible. The 'IsString' instance parses a closed
-- term; 'parseOpen' takes a scope and an environment for the free variables.
module LambdaLet.Parser
  ( parseLambdaLet
  , parseOpen
  , resolve
  , withFreeVars
  ) where

import Data.String (IsString (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.Foil
import Demo.Parsing (parseWith, resolveWith, withFreeVars)
import LambdaLet (LambdaLet)
import LambdaLet.Generated (toTerm)
import LambdaLet.Syntax.Abs (Term, VarIdent (..))
import LambdaLet.Syntax.Par (myLexer, pTerm)

-- | Resolve a raw term into scope-safe syntax; a free variable missing from
-- the environment is an error.
resolve :: Distinct n => Scope n -> Map String (Name n) -> Term -> LambdaLet n
resolve = resolveWith toTerm VarIdent

-- | Parse a term in a scope, given the names of the variables in it.
parseOpen :: Distinct n => Scope n -> Map String (Name n) -> String -> Either String (LambdaLet n)
parseOpen = parseWith (pTerm . myLexer) toTerm VarIdent

-- | Parse a closed term.
parseLambdaLet :: String -> Either String (LambdaLet VoidS)
parseLambdaLet = parseOpen emptyScope Map.empty

instance IsString (LambdaLet VoidS) where
  fromString = either (error . ("LambdaLet.Parser: " ++)) id . parseLambdaLet
