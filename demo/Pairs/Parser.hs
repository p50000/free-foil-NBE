{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Parsing pairs terms from strings: the BNFC-generated lexer and parser
-- plus free-foil's generated scope resolution. @(a, b)@ is a pair, @fst t@
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
import qualified Data.Map.Strict as Map

import Control.Monad.Foil
import Pairs (Pairs)
import Pairs.Generated (toTerm)
import Pairs.Syntax.Abs (Term, VarIdent (..))
import Pairs.Syntax.Par (myLexer, pTerm)

-- | Resolve a raw term into scope-safe syntax; a free variable missing from
-- the environment is an error.
resolve :: Distinct n => Scope n -> Map String (Name n) -> Term -> Pairs n
resolve scope env = toTerm scope (Map.mapKeys VarIdent env)

-- | Parse a term in a scope, given the names of the variables in it.
parseOpen :: Distinct n => Scope n -> Map String (Name n) -> String -> Either String (Pairs n)
parseOpen scope env s = resolve scope env <$> (pTerm . myLexer) s

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
