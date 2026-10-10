{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
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
-- one 'Eval' instance (β), and a substitution-based reference normaliser.
module LambdaPi
  ( LambdaPi
  , pattern Var
  , pattern App
  , pattern Lam
  , pattern Pi
  , Value
  , eval
  , nfNbe
  , whnfNbe
  , whnf
  , nf
  , nfd
  , two
  , appTwo
  , neutralNbeOk
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import FreeFoil.NbE (Eval (..), eval, nfNbe, whnfNbe)
import qualified FreeFoil.NbE as NbE

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
-- needs its own pragma, since the nfNbe one alone leaves eval passing
-- dictionaries. The quote pragmas do not take effect yet: the specialised
-- nfNbe still calls the generic quote worker with the dictionaries.
{-# SPECIALIZE NbE.nfNbe :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o ->
      Substitution (NbE.Value FFPattern TermSig) i o ->
      LambdaPi i ->
      NbE.Value FFPattern TermSig o #-}
{-# SPECIALIZE NbE.quote ::
      Distinct n => Scope n -> NbE.Value FFPattern TermSig n -> LambdaPi n #-}
{-# SPECIALIZE NbE.quoteSuspendedScoped ::
      (Distinct n, Distinct i) =>
      Scope n ->
      Substitution (NbE.Value FFPattern TermSig) i n ->
      ScopedAST FFPattern TermSig i ->
      ScopedAST FFPattern TermSig n #-}

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
instance Eval FFPattern TermSig where
  evalSig scope env = \case
    AppSig fun arg ->
      case eval scope env fun of
        NbE.VSuspended env' (LamSig (ScopedAST (FFPatternVar binder) body)) ->
          case assertDistinct binder of
            Distinct -> eval scope (addSubst env' binder (eval scope env arg)) body
        fun' -> NbE.VNode (AppSig fun' (eval scope env arg))
    node -> NbE.evalNode (eval scope) env node

-- | Weak-head normal form by substitution, the reference for the tests.
whnf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
whnf scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = addSubst identitySubst binder arg
        in whnf scope (substitute scope subst body)
      fun' -> App fun' arg
  t -> t

-- | Normal form by substitution.
nf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
nf scope = \case
  Lam binder body ->
    case assertDistinct binder of
      Distinct ->
        let scope' = extendScope binder scope
        in Lam binder (nf scope' body)
  Pi dom binder body ->
    case assertDistinct binder of
      Distinct ->
        let scope' = extendScope binder scope
        in Pi (nf scope dom) binder (nf scope' body)
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = addSubst identitySubst binder arg
        in nf scope (substitute scope subst body)
      fun' -> App (nf scope fun') (nf scope arg)
  t -> t

-- | 'nf' in the empty scope.
nfd :: LambdaPi VoidS -> LambdaPi VoidS
nfd = nf emptyScope

-- | The Church numeral two.
two :: LambdaPi VoidS
two = withFresh emptyScope
  (\ s -> Lam s $ withFresh (extendScope s emptyScope)
    (\ z -> Lam z (App (Var (sink (nameOf s)))
                       (App (Var (sink (nameOf s)))
                            (Var (nameOf z))))))

-- | Church two applied to itself, i.e. four.
appTwo :: LambdaPi VoidS
appTwo = App two two

-- | In a scope with free @f@ and @g@, @f ((λx. x) g)@ normalises to the
-- neutral @f g@: the argument's redex is reduced, the stuck application stays.
neutralNbeOk :: Bool
neutralNbeOk =
  withFresh emptyScope $ \fBinder ->
    withFresh (extendScope fBinder emptyScope) $ \gBinder ->
      let scope = extendScope gBinder (extendScope fBinder emptyScope)
          f = sink (nameOf fBinder)
          g = nameOf gBinder
          idLam = withFresh scope (\x -> Lam x (Var (nameOf x)))
          term = App (Var f) (App idLam (Var g))
      in case nfNbe scope term of
           App (Var f') (Var g') -> f' == f && g' == g
           _                     -> False
