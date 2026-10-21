{-# LANGUAGE RankNTypes #-}
-- | Parsing shared by the demonstration languages: a BNFC parser followed by
-- free-foil's generated scope resolution, in a scope whose free variables
-- have names.
module Demo.Parsing
  ( resolveWith
  , parseWith
  , withFreeVars
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.Foil

-- | Resolve a raw term in a scope with free-foil's generated conversion,
-- given the names of the free variables. Each grammar generates its own
-- identifier type, so its constructor comes as an argument.
resolveWith ::
  Ord ident =>
  (Scope n -> Map ident (Name n) -> raw -> ast) ->
  (String -> ident) ->
  Scope n -> Map String (Name n) -> raw -> ast
resolveWith toAST ident scope env = toAST scope (Map.mapKeys ident env)

-- | Parse a string and resolve it in a scope.
parseWith ::
  Ord ident =>
  (String -> Either String raw) ->
  (Scope n -> Map ident (Name n) -> raw -> ast) ->
  (String -> ident) ->
  Scope n -> Map String (Name n) -> String -> Either String ast
parseWith parse toAST ident scope env s = resolveWith toAST ident scope env <$> parse s

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
