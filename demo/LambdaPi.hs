{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- The 'Eval TermSig' instance lives here, with the language's dynamics (next to
-- the reference 'nf'), rather than in the generated-syntax module.
{-# OPTIONS_GHC -Wno-orphans #-}

-- | The lambda-pi demonstration language.
--
-- The scope-safe syntax, its signature bifunctor, and the raw/scoped
-- conversions are generated from "LambdaPi.Raw" by free-foil's Template
-- Haskell (see "LambdaPi.Generated"). This module only adds the friendly
-- surface API — a 'LambdaPi' type synonym and 'Var'\/'App'\/'Lam'\/'Pi'
-- pattern synonyms that hide the generated @FFPattern@ wrapper — and the
-- normalisers ('nf', 'whnf', and the NbE-based 'nfNbe').
module LambdaPi
  ( LambdaPi,
    pattern Var,
    pattern App,
    pattern Lam,
    pattern Pi,
    whnf,
    nf,
    nfd,
    Value,
    eval,
    nfNbe,
    whnfNbe,
    two,
    appTwo,
    neutralNbeOk,
  )
where

import FreeFoil.NbE
    ( S(VoidS),
      Distinct,
      Scope,
      NameBinder,
      AST(Var),
      ScopedAST(ScopedAST),
      DistinctEvidence(Distinct),
      ScopedClosure(ScopedClosure),
      Eval(..),
      eval,
      nfNbe,
      whnfNbe,
      assertDistinct,
      sink,
      nameOf,
      addSubst,
      emptyScope,
      extendScope,
      identitySubst,
      withFresh,
      substitute
    )
import qualified FreeFoil.NbE as NbE

import LambdaPi.Generated
    ( FFTerm,
      TermSig(AppSig, LamSig),
      FFPattern(FFPatternVar),
      pattern FFApp,
      pattern FFLam,
      pattern FFPi
    )

-- | Scope-safe lambda-pi terms in scope @n@ (an alias for the generated
-- @FFTerm@).
type LambdaPi n = FFTerm n

-- Force the generic normaliser to be specialized to this concrete signature at
-- the library boundary (see the perf investigation): without this the recursive
-- eval/quote loop is dictionary-passing. The loop functions are specialized
-- individually — the nfNbe pragma alone does not devirtualise the recursive
-- eval/evalSig calls (visible as class-op selector time in profiles).
{-# SPECIALIZE NbE.nfNbe :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o ->
      NbE.Substitution (NbE.Value FFPattern TermSig) i o ->
      LambdaPi i ->
      NbE.Value FFPattern TermSig o #-}
{-# SPECIALIZE NbE.quote ::
      Distinct n => Scope n -> NbE.Value FFPattern TermSig n -> LambdaPi n #-}
{-# SPECIALIZE NbE.quoteScopedClosure ::
      Distinct n =>
      Scope n ->
      NbE.ScopedClosure FFPattern TermSig n ->
      ScopedAST FFPattern TermSig n #-}

-- | Application. (@Var@ is re-exported from free-foil's generic 'AST'.)
pattern App :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern App fun arg = FFApp fun arg

-- | Lambda abstraction. Hides the generated @FFPatternVar@ wrapper so the body
-- binds a plain 'NameBinder', as before.
pattern Lam :: NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Lam binder body = FFLam (FFPatternVar binder) body

-- | Dependent function type @(x : dom) -> body@. The domain @dom@ lives in the
-- outer scope @n@; the codomain @body@ may mention the bound variable.
pattern Pi :: LambdaPi n -> NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Pi dom binder body = FFPi dom (FFPatternVar binder) body

{-# COMPLETE Var, App, Lam, Pi #-}

--- Impl of nf, whnf using generic sinking
whnf :: Distinct n => Scope n -> LambdaPi n -> LambdaPi n
whnf scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = addSubst identitySubst binder arg
        in whnf scope (substitute scope subst body)
      fun' -> App fun' arg
  t -> t

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

nfd :: LambdaPi VoidS -> LambdaPi VoidS
nfd = nf emptyScope

--- Impl of nf, whnf using NBE
type Value = NbE.Value FFPattern TermSig

-- | Lambda-pi as an NbE instance. The entire object-language contribution is
-- its one elimination rule, application: introduction forms (@Lam@, @Pi@) have
-- no elimination rule and fall through to the generic default, which rebuilds
-- them as a 'NbE.VNode'. So a @Pi@ keeps its domain as an eager value and its
-- codomain as a suspended 'ScopedClosure' (see 'NbE.Value'). The semantic
-- 'FreeFoil.NbE.eval' \/ 'FreeFoil.NbE.quote' and the derived
-- 'FreeFoil.NbE.nfNbe' (both re-exported above) come for free.
--
-- 'evalSig' receives the raw node and the current environment. The 'AppSig'
-- case evaluates the function itself; beta-reduction re-evaluates the lambda
-- body under the captured environment extended with the (lazily evaluated)
-- argument, and a function stuck on a neutral stays a 'NbE.VNode' application.
-- This is the only place that establishes the 'NbE.Value' invariant (no
-- introduction form is ever applied to an argument).
instance Eval FFPattern TermSig where
  evalSig scope env = \case
    AppSig fun arg ->
      case eval scope env fun of
        NbE.VNode (LamSig (ScopedClosure env' (FFPatternVar binder) body)) ->
          case assertDistinct binder of
            Distinct -> eval scope (addSubst env' binder (eval scope env arg)) body
        fun' -> NbE.VNode (AppSig fun' (eval scope env arg))
    node -> NbE.evalNode (eval scope) env node

--- examples
two :: LambdaPi VoidS
two = withFresh emptyScope
  (\ s -> Lam s $ withFresh (extendScope s emptyScope)
    (\ z -> Lam z (App (Var (sink (nameOf s)))
                       (App (Var (sink (nameOf s)))
                            (Var (nameOf z))))))

appTwo :: LambdaPi VoidS
appTwo = App two two

-- | NbE must preserve neutral terms built from free variables.
--
-- In a scope with two free variables @f@ and @g@, the term @f ((λx. x) g)@
-- normalises to the neutral application @f g@: the redex in the argument is
-- reduced while the application stuck on the free @f@ is preserved.
neutralNbeOk :: Bool
neutralNbeOk =
  withFresh emptyScope $ \fBinder ->
    withFresh (extendScope fBinder emptyScope) $ \gBinder ->
      let scope = extendScope gBinder (extendScope fBinder emptyScope)
          f = sink (nameOf fBinder)  -- free variable f, sunk into the full scope
          g = nameOf gBinder         -- free variable g
          idLam = withFresh scope (\x -> Lam x (Var (nameOf x)))
          term = App (Var f) (App idLam (Var g))
      in case nfNbe scope term of
           App (Var f') (Var g') -> f' == f && g' == g
           _                     -> False
