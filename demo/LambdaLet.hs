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

-- | The lambda-let demonstration language: the untyped lambda-calculus plus
-- @let@ — the first feature of the zoo series (see @FEATURE_ZOO_DESIGN.md@,
-- "Let \/ definitions").
--
-- @let@ is the simplest binding construct after lambda, and it is an
-- /eliminator that always fires/: @let x = e in b@ evaluates @b@ under the
-- environment extended with @x ↦ eval e@ — structurally identical to a beta
-- step, except the redex is always present. Consequently @let@ never appears
-- in a normal form and needs no neutral case, no new framework machinery, and
-- no change to quoting.
--
-- The scope-safe syntax is generated from @demo/grammar/LambdaLet/Syntax.cf@
-- via BNFC and free-foil's Template Haskell (see "LambdaLet.Generated"). This
-- module adds the friendly surface API — pattern synonyms hiding the generated
-- @FFPattern@ wrapper — the one 'Eval' instance, and a reference
-- substitution-based normaliser used as the test oracle. Example terms live in
-- "LambdaLet.Examples".
module LambdaLet
  ( LambdaLet,
    pattern Var,
    pattern App,
    pattern Lam,
    pattern Let,
    Value,
    eval,
    nfNbe,
    whnfNbe,
    nf,
    whnf,
  )
where

import FreeFoil.NbE
  ( AST (Var),
    Distinct,
    DistinctEvidence (Distinct),
    Eval (..),
    NameBinder,
    Scope,
    ScopedAST (ScopedAST),
    addSubst,
    assertDistinct,
    eval,
    extendScope,
    identitySubst,
    nfNbe,
    substitute,
    whnfNbe,
  )
import qualified FreeFoil.NbE as NbE

import LambdaLet.Generated
  ( FFPattern (FFPatternVar),
    FFTerm,
    TermSig (AppSig, LamSig, LetSig),
    pattern FFApp,
    pattern FFLam,
    pattern FFLet,
  )

-- | Scope-safe lambda-let terms in scope @n@ (an alias for the generated
-- @FFTerm@).
type LambdaLet n = FFTerm n

-- Specialize the generic normaliser to this concrete signature at the library
-- boundary; see the twin pragmas in "LambdaPi" for why each loop function
-- needs its own pragma.
{-# SPECIALIZE NbE.nfNbe :: Distinct n => Scope n -> LambdaLet n -> LambdaLet n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o ->
      NbE.Substitution (NbE.Value FFPattern TermSig) i o ->
      LambdaLet i ->
      NbE.Value FFPattern TermSig o #-}
{-# SPECIALIZE NbE.quote ::
      Distinct n => Scope n -> NbE.Value FFPattern TermSig n -> LambdaLet n #-}
{-# SPECIALIZE NbE.quoteSuspendedScoped ::
      (Distinct n, Distinct i) =>
      Scope n ->
      NbE.Substitution (NbE.Value FFPattern TermSig) i n ->
      ScopedAST FFPattern TermSig i ->
      ScopedAST FFPattern TermSig n #-}

-- | Application. (@Var@ is re-exported from free-foil's generic 'AST'.)
pattern App :: LambdaLet n -> LambdaLet n -> LambdaLet n
pattern App fun arg = FFApp fun arg

-- | Lambda abstraction. Hides the generated @FFPatternVar@ wrapper so the body
-- binds a plain 'NameBinder'.
pattern Lam :: NameBinder n l -> LambdaLet l -> LambdaLet n
pattern Lam binder body = FFLam (FFPatternVar binder) body

-- | @let x = e in body@. The bound expression @e@ lives in the outer scope
-- @n@; the body may mention the bound variable.
pattern Let :: LambdaLet n -> NameBinder n l -> LambdaLet l -> LambdaLet n
pattern Let e binder body = FFLet e (FFPatternVar binder) body

{-# COMPLETE Var, App, Lam, Let #-}

-- | Semantic values of lambda-let.
type Value = NbE.Value FFPattern TermSig

-- | Lambda-let as an NbE instance: two elimination rules.
--
-- 'AppSig' is beta, exactly as in "LambdaPi": evaluate the function, and on a
-- suspended lambda re-enter its body under the captured environment extended
-- with the argument's value; stuck on a neutral, rebuild the application.
--
-- 'LetSig' is the cut: it /always/ reduces — the body is evaluated under the
-- current environment extended with the bound expression's value, exactly as
-- beta evaluates a lambda body. There is no stuck case (nothing to inspect,
-- nothing to be neutral in), so a @let@ never survives into a value and the
-- generic quote needs no extension. Note the bound expression is evaluated
-- lazily, /at most once/: the environment entry is a thunk, shared by every
-- occurrence of @x@ — forced the first time @x@ is looked up, never if the
-- binding is unused (even a divergent bound expression is harmless then).
-- A substitution-based normaliser (see 'nf') has neither property: it copies
-- the unevaluated expression into every occurrence and reduces each copy.
--
-- 'LamSig' is the sole introduction form and falls through to the generic
-- default.
instance Eval FFPattern TermSig where
  evalSig scope env = \case
    AppSig fun arg ->
      case eval scope env fun of
        NbE.VSuspended env' (LamSig (ScopedAST (FFPatternVar binder) body)) ->
          case assertDistinct binder of
            Distinct -> eval scope (addSubst env' binder (eval scope env arg)) body
        fun' -> NbE.VNode (AppSig fun' (eval scope env arg))
    LetSig e (ScopedAST (FFPatternVar binder) body) ->
      case assertDistinct binder of
        Distinct -> eval scope (addSubst env binder (eval scope env e)) body
    node -> NbE.evalNode (eval scope) env node

-- Reference normalisers (substitution-based), used as the test oracle. -------

-- | Weak-head normal form by explicit substitution: @let@ substitutes its
-- bound expression into the body /unevaluated/ (call-by-name), then reduction
-- continues on the result.
whnf :: Distinct n => Scope n -> LambdaLet n -> LambdaLet n
whnf scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = addSubst identitySubst binder arg
        in whnf scope (substitute scope subst body)
      fun' -> App fun' arg
  Let e binder body ->
    let subst = addSubst identitySubst binder e
    in whnf scope (substitute scope subst body)
  t -> t

-- | Normal form by explicit substitution. The @let@ case discards the binding
-- after substituting, so — like NbE — no @let@ survives in a normal form; the
-- two normalisers must agree up to alpha-equivalence.
nf :: Distinct n => Scope n -> LambdaLet n -> LambdaLet n
nf scope = \case
  Lam binder body ->
    case assertDistinct binder of
      Distinct ->
        let scope' = extendScope binder scope
        in Lam binder (nf scope' body)
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = addSubst identitySubst binder arg
        in nf scope (substitute scope subst body)
      fun' -> App (nf scope fun') (nf scope arg)
  Let e binder body ->
    let subst = addSubst identitySubst binder e
    in nf scope (substitute scope subst body)
  t -> t
