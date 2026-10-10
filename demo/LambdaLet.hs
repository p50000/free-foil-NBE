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
-- | The lambda-let demonstration language: the untyped lambda calculus with
-- @let@. The syntax is generated in "LambdaLet.Generated"; this module adds
-- pattern synonyms over it, the 'Eval' instance, and a substitution-based
-- reference normaliser. Example terms are in "LambdaLet.Examples".
module LambdaLet
  ( LambdaLet
  , pattern Var
  , pattern App
  , pattern Lam
  , pattern Let
  , Value
  , eval
  , nfNbe
  , whnfNbe
  , nf
  , whnf
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import FreeFoil.NbE (Eval (..), eval, nfNbe, whnfNbe)
import qualified FreeFoil.NbE as NbE

import LambdaLet.Generated
  ( FFPattern (FFPatternVar)
  , FFTerm
  , TermSig (AppSig, LamSig, LetSig)
  , pattern FFApp
  , pattern FFLam
  , pattern FFLet
  )

-- | Scope-safe lambda-let terms in scope @n@.
type LambdaLet n = FFTerm n

-- Specialise the generic loop to this signature, as in "LambdaPi".
{-# SPECIALIZE NbE.nfNbe :: Distinct n => Scope n -> LambdaLet n -> LambdaLet n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o ->
      Substitution (NbE.Value FFPattern TermSig) i o ->
      LambdaLet i ->
      NbE.Value FFPattern TermSig o #-}
{-# SPECIALIZE NbE.quote ::
      Distinct n => Scope n -> NbE.Value FFPattern TermSig n -> LambdaLet n #-}
{-# SPECIALIZE NbE.quoteSuspendedScoped ::
      (Distinct n, Distinct i) =>
      Scope n ->
      Substitution (NbE.Value FFPattern TermSig) i n ->
      ScopedAST FFPattern TermSig i ->
      ScopedAST FFPattern TermSig n #-}

-- | Application.
pattern App :: LambdaLet n -> LambdaLet n -> LambdaLet n
pattern App fun arg = FFApp fun arg

-- | Lambda abstraction; the binder is a plain 'NameBinder'.
pattern Lam :: NameBinder n l -> LambdaLet l -> LambdaLet n
pattern Lam binder body = FFLam (FFPatternVar binder) body

-- | @let x = e in body@; the bound expression lives in the outer scope.
pattern Let :: LambdaLet n -> NameBinder n l -> LambdaLet l -> LambdaLet n
pattern Let e binder body = FFLet e (FFPatternVar binder) body

{-# COMPLETE Var, App, Lam, Let #-}

-- | Semantic values of lambda-let.
type Value = NbE.Value FFPattern TermSig

-- | Two elimination rules. Application is β, as in "LambdaPi". @let@ always
-- reduces: the body is evaluated under the environment extended with the
-- bound expression, exactly as β enters a lambda body, so no @let@ survives
-- into a value and readback needs no case for it. The bound expression is a
-- thunk in the environment: evaluated at most once, shared by every use, and
-- never if unused. The reference 'nf' substitutes it unevaluated into every
-- occurrence instead.
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

-- | Weak-head normal form by substitution; @let@ substitutes its bound
-- expression unevaluated.
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

-- | Normal form by substitution. No @let@ survives here either, so the two
-- normalisers must agree up to α.
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
