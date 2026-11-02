{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}
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
import Data.Bifunctor (bimap)
import FreeFoil.NbE (Eval (..), HasDefinitions, HasHeads (..))
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
{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> NbE.NoContext n -> LambdaPi n -> LambdaPi n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o ->
      NbE.NoContext o ->
      Substitution (NbE.Value FFPattern TermSig) i o ->
      LambdaPi i ->
      NbE.Value FFPattern TermSig o #-}
{-# SPECIALIZE NbE.quote ::
      Distinct n => Scope n -> NbE.NoContext n -> NbE.Value FFPattern TermSig n -> LambdaPi n #-}
{-# SPECIALIZE Conv.conv ::
      Distinct n =>
      Scope n -> NbE.NoContext n -> NbE.Value FFPattern TermSig n -> NbE.Value FFPattern TermSig n -> Bool #-}
{-# SPECIALIZE Conv.convertible :: Distinct n => Scope n -> NbE.NoContext n -> LambdaPi n -> LambdaPi n -> Bool #-}

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

-- | The heads: the function of an application.
instance HasHeads TermSig where
  {-# INLINE headsWith #-}
  headsWith hd other = \case
    AppSig fun arg -> AppSig (hd fun) (other arg)
    node           -> bimap id other node

-- | The one elimination rule, application. A suspended lambda is entered
-- under its captured environment extended with the argument; a neutral head
-- rebuilds the application. @Lam@ and @Pi@ fall through to the default, so a
-- @Pi@ keeps its domain as a value and its codomain suspended.
instance (Sinkable ctx, HasDefinitions ctx FFPattern TermSig) => Eval ctx FFPattern TermSig where
  {-# INLINABLE evalSig #-}
  evalSig scope ctx env = \case
    AppSig fun arg -> appValue scope ctx (NbE.eval scope ctx env fun) (NbE.eval scope ctx env arg)
    node -> NbE.evalNode scope ctx env node

  {-# INLINE etaMatchWith #-}
  etaMatchWith scoped _ = \case
    LamSig body -> Just (LamSig (scoped body (NbE.EtaScoped (\scope ctx (FFPatternVar x) other ->
      appValue scope ctx other (NbE.vvar (nameOf x))))))
    _ -> Nothing

-- | Apply a function value to an argument value: a suspended lambda is
-- entered under its environment extended with the argument, any other
-- function is a stuck application.
appValue :: (Eval ctx FFPattern TermSig, Distinct n) => Scope n -> ctx n -> Value n -> Value n -> Value n
-- The helper takes the context, so it is inlined into the rules and
-- specialised with them at every context. A call with a bound 'Distinct'
-- dictionary is not specialised on its own.
{-# INLINE appValue #-}
appValue scope ctx fun arg = NbE.eliminate fun $ \case
  NbE.VSuspended env' (LamSig (ScopedAST (FFPatternVar binder) body)) ->
    case assertDistinct binder of
      Distinct -> NbE.eval scope ctx (addSubst env' binder arg) body
  NbE.Stuck fun' -> NbE.vnode (AppSig fun' arg)

-- | Evaluation in a scope, with no other context.
eval :: (Distinct o, Distinct i) => Scope o -> Substitution Value i o -> LambdaPi i -> Value o
{-# INLINE eval #-}
eval scope = NbE.eval scope NbE.NoContext

-- | Normal form in a scope, with no other context.
nf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
{-# INLINE nf #-}
nf scope = NbE.nf scope NbE.NoContext

-- | Weak-head normal form in a scope, with no other context.
whnf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
{-# INLINE whnf #-}
whnf scope = NbE.whnf scope NbE.NoContext

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
