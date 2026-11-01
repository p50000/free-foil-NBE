{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
-- | The fragment of functions: lambda, application and the dependent
-- function type. Its one rule is β, and its one η law is that of lambdas,
-- both as in "LambdaPi" and written for any language that contains the
-- fragment and any binder: a suspended lambda is entered under its captured
-- environment extended with the argument, a neutral head rebuilds the
-- application, and @Pi@ falls through to the default. The binder of a
-- lambda is expected to bind one name. Applying a lambda whose pattern binds
-- two fails in 'addSubstPattern', and so does its η law.
module Fragments.Lambda
  ( LamF (..)
  , appValue
  ) where

import Control.DeepSeq        (NFData)
import Control.Monad.Foil
import Control.Monad.Free.Foil
import Data.Bifunctor.TH       (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.ZipMatchK.TH       (deriveZipMatchK)
import GHC.Generics            (Generic)

import FreeFoil.NbE            (EtaScoped (..), Eval, HasHeads, Value (..), eval, evalNode)
import FreeFoil.NbE.Sum

-- | Functions: @λx. t@, @t u@ and @Π (x : a). b@.
data LamF scope term
  = LamF scope
  | AppF term term
  | PiF term scope
  deriving (Functor, Generic)

deriveBifunctor ''LamF
deriveBifoldable ''LamF
deriveBitraversable ''LamF

deriveZipMatchK ''LamF
instance (NFData scope, NFData term) => NFData (LamF scope term)

-- | No heads: the fragment does not refine values.
instance HasHeads LamF

instance (Sinkable ctx, CoSinkable binder) => EvalF ctx binder LamF where
  {-# INLINE evalF #-}
  evalF pos scope ctx env = \case
    AppF fun arg -> appValue pos scope ctx (eval scope ctx env fun) (eval scope ctx env arg)
    node -> evalNode scope ctx env (inj pos node)

  {-# INLINE etaMatchWithF #-}
  etaMatchWithF pos scoped _ = \case
    LamF body -> Just (LamF (scoped body (EtaScoped (\scope ctx binder other ->
      case namesOfPattern binder of
        [x] -> appValue pos scope ctx other (VVar x)
        _   -> error "Fragments.Lambda: the η law of a lambda needs a pattern that binds one name"))))
    _ -> Nothing

-- | Apply a function value to an argument value in a language containing
-- the fragment: a suspended lambda of the fragment is entered under its
-- environment extended with the argument, any other function is a stuck
-- application.
appValue ::
  (Eval ctx binder sig, CoSinkable binder, Distinct n) =>
  Inj LamF sig -> Scope n -> ctx n -> Value binder sig n -> Value binder sig n -> Value binder sig n
{-# INLINE appValue #-}
appValue pos scope ctx fun arg = case fun of
  VSuspended env' node
    | Just (LamF (ScopedAST binder body)) <- prj pos node ->
        case assertDistinct binder of
          Distinct -> eval scope ctx (addSubstPattern env' binder [arg]) body
  _ -> VNode (inj pos (AppF fun arg))
