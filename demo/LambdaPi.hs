{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
-- The Eval instance is an orphan on purpose: it belongs with the language's
-- dynamics, next to the reference normaliser.
{-# OPTIONS_GHC -Wno-orphans #-}
-- | The lambda-pi demonstration language: the untyped lambda calculus with
-- the dependent function type @Pi@ as a term former. The syntax is generated
-- in "LambdaPi.Generated"; this module adds pattern synonyms over it, the
-- one 'Eval' instance (β, and the η law of lambdas for conversion checking),
-- and a substitution-based reference normaliser. Example terms are in
-- "LambdaPi.Examples".
module LambdaPi
  ( LambdaPi
  , pattern Var
  , pattern App
  , pattern Lam
  , pattern Pi
  , Value
  , eval
  , nf
  , whnf
  , whnfSubst
  , nfSubst
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import FreeFoil.NbE (Context, Eval (..), eval, nf, whnf)
import qualified FreeFoil.NbE as NbE
import qualified FreeFoil.NbE.Conversion as Conv

import LambdaPi.Generated
  ( FFPattern (FFPatternVar)
  , FFTerm
  , TermSig (AppSig, LamSig)
  , pattern FFApp
  , pattern FFLam
  , pattern FFPi
  )

-- | Scope-safe lambda-pi terms in scope @n@.
type LambdaPi n = FFTerm n

-- Specialise the generic loop to this signature. Each recursive function
-- needs its own pragma, since the nf one alone leaves eval and quote passing
-- dictionaries.
{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o ->
      Substitution (NbE.Value FFPattern TermSig) i o ->
      LambdaPi i ->
      NbE.Value FFPattern TermSig o #-}
{-# SPECIALIZE NbE.quote ::
      Distinct n => Scope n -> NbE.Value FFPattern TermSig n -> LambdaPi n #-}
{-# SPECIALIZE Conv.conv ::
      Distinct n =>
      Scope n -> NbE.Value FFPattern TermSig n -> NbE.Value FFPattern TermSig n -> Bool #-}
{-# SPECIALIZE Conv.convertible :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n -> Bool #-}

-- | Application.
pattern App :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern App fun arg = FFApp fun arg

-- | Lambda abstraction; the binder is a plain 'NameBinder'.
pattern Lam :: NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Lam binder body = FFLam (FFPatternVar binder) body

-- | Dependent function type @(x : dom) -> body@; the domain lives in the
-- outer scope.
pattern Pi :: LambdaPi n -> NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Pi dom binder body = FFPi dom (FFPatternVar binder) body

{-# COMPLETE Var, App, Lam, Pi #-}

-- | Semantic values of lambda-pi.
type Value = NbE.Value FFPattern TermSig

-- | The one elimination rule, application. A suspended lambda is entered
-- under its captured environment extended with the argument; a neutral head
-- rebuilds the application. @Lam@ and @Pi@ fall through to the default, so a
-- @Pi@ keeps its domain as a value and its codomain suspended.
instance Context ctx => Eval ctx FFPattern TermSig where
  evalSig ctx env = \case
    AppSig fun arg -> appValue ctx (eval ctx env fun) (eval ctx env arg)
    node -> NbE.evalNode ctx env node

  etaMatchWith scoped _ = \case
    LamSig body -> Just (LamSig (scoped body (NbE.EtaScoped (\ctx (FFPatternVar x) other ->
      appValue ctx other (NbE.VVar (nameOf x))))))
    _ -> Nothing

-- | Apply a function value to an argument value: a suspended lambda is
-- entered under its environment extended with the argument, any other
-- function is a stuck application.
appValue :: (Context ctx, Distinct n) => ctx n -> Value n -> Value n -> Value n
appValue ctx fun arg = case fun of
  NbE.VSuspended env' (LamSig (ScopedAST (FFPatternVar binder) body)) ->
    case assertDistinct binder of
      Distinct -> eval ctx (addSubst env' binder arg) body
  _ -> NbE.VNode (AppSig fun arg)

-- | Weak-head normal form by substitution, the reference for the tests.
whnfSubst :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
whnfSubst scope = \case
  App fun arg ->
    case whnfSubst scope fun of
      Lam binder body ->
        let subst = addSubst identitySubst binder arg
        in whnfSubst scope (substitute scope subst body)
      fun' -> App fun' arg
  t -> t

-- | Normal form by substitution.
nfSubst :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
nfSubst scope = \case
  Lam binder body ->
    case assertDistinct binder of
      Distinct ->
        let scope' = extendScope binder scope
        in Lam binder (nfSubst scope' body)
  Pi dom binder body ->
    case assertDistinct binder of
      Distinct ->
        let scope' = extendScope binder scope
        in Pi (nfSubst scope dom) binder (nfSubst scope' body)
  App fun arg ->
    case whnfSubst scope fun of
      Lam binder body ->
        let subst = addSubst identitySubst binder arg
        in nfSubst scope (substitute scope subst body)
      fun' -> App (nfSubst scope fun') (nfSubst scope arg)
  t -> t
