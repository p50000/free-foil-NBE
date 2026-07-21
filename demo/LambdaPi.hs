{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
      Substitution,
      Closure(..),
      assertDistinct,
      sink,
      nameOf,
      addSubst,
      emptyScope,
      extendScope,
      identitySubst,
      withFresh,
      substitute,
      lookupSubst,
      quote',
      quoteScoped
    )

import LambdaPi.Generated
    ( FFTerm,
      TermSig(AppSig, LamSig, PiSig),
      FFPattern(FFPatternVar),
      pattern FFApp,
      pattern FFLam,
      pattern FFPi
    )

-- | Scope-safe lambda-pi terms in scope @n@ (an alias for the generated
-- @FFTerm@).
type LambdaPi n = FFTerm n

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
type Value = Closure FFPattern TermSig

eval :: (Distinct o, Distinct i) => Scope o -> Substitution Value i o -> LambdaPi i -> Value o
eval scope env = \case
  Var x -> lookupSubst env x
  FFApp f x ->
    let fun = eval scope env f
        arg = eval scope env x
      in case fun of
        Closure env' (LamSig (ScopedAST (FFPatternVar binder) body)) ->
          case assertDistinct binder of
            Distinct ->
              let env'' = addSubst env' binder arg
              in eval scope env'' body
        fun' -> Closure identitySubst (AppSig fun' arg)
  FFLam pat body ->
    Closure env (LamSig (ScopedAST pat body))
  FFPi dom pat body ->
    -- 'Pi' carries both a term position (the domain) and a scoped position
    -- (the codomain), which must share one environment. We therefore evaluate
    -- the domain eagerly under @env@ and normalise the codomain into the same
    -- scope via the generic 'quoteScoped', then suspend the whole (now closed
    -- over the identity substitution) node.
    Closure identitySubst
      (PiSig (eval scope env dom)
             (quoteScoped eval scope env (ScopedAST pat body)))

-- | Normal form via NbE: evaluate into the semantic domain, then quote back.
--
-- Agrees with the reference substitution-based 'nf' on lambda-pi terms (see
-- the test suite). For example, @(λx. x) (λy. y)@ normalises to @λy. y@ and the
-- dependent type @(x : A) -> (λy. y) x@ normalises to @(x : A) -> x@.
nfNbe :: (Distinct n) => Scope n -> LambdaPi n -> LambdaPi n
nfNbe scope term = quote' eval scope (eval scope identitySubst term)

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
