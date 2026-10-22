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
-- | The naturals demonstration language: @zero@, @suc@ and primitive
-- recursion, @natrec n { zero -> z ; suc k, r -> s }@, whose @suc@ branch
-- binds the predecessor @k@ and the recursive result @r@ with one pattern.
-- There are no functions, so every term normalises. The syntax is generated
-- in "Naturals.Generated"; this module adds pattern synonyms over it, the
-- 'Eval' instance, and a substitution-based reference normaliser. Example
-- terms are in "Naturals.Examples".
--
-- New against the other languages: an eliminator with a scoped branch that
-- recurses on the value of its scrutinee, and binds the recursive result in
-- the environment as a thunk, forced only if the branch uses it and shared
-- by every use.
module Naturals
  ( Naturals
  , pattern Var
  , pattern Zero
  , pattern Suc
  , pattern NatRec
  , numeral
  , Value
  , eval
  , nf
  , whnf
  , nfSubst
  , whnfSubst
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import FreeFoil.NbE (Eval (..), eval, nf, whnf)
import qualified FreeFoil.NbE as NbE
import qualified FreeFoil.NbE.Conversion as Conv

import Naturals.Generated
  ( FFPattern (FFPatternRec)
  , FFTerm
  , TermSig (NatRecSig, SucSig, ZeroSig)
  , pattern FFNatRec
  , pattern FFSuc
  , pattern FFZero
  )

-- | Scope-safe naturals terms in scope @n@.
type Naturals n = FFTerm n

-- Specialise the generic loop to this signature, as in "LambdaPi".
{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> Naturals n -> Naturals n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o ->
      Substitution (NbE.Value FFPattern TermSig) i o ->
      Naturals i ->
      NbE.Value FFPattern TermSig o #-}
{-# SPECIALIZE NbE.quote ::
      Distinct n => Scope n -> NbE.Value FFPattern TermSig n -> Naturals n #-}
{-# SPECIALIZE Conv.conv :: Distinct n => Scope n -> Value n -> Value n -> Bool #-}
{-# SPECIALIZE Conv.convertible :: Distinct n => Scope n -> Naturals n -> Naturals n -> Bool #-}

-- | @zero@.
pattern Zero :: Naturals n
pattern Zero = FFZero

-- | @suc n@.
pattern Suc :: Naturals n -> Naturals n
pattern Suc n = FFSuc n

-- | @natrec n { zero -> z ; suc k, r -> s }@; @r@ is bound in the scope of
-- @k@.
pattern NatRec
  :: Naturals n -> Naturals n -> NameBinder n i -> NameBinder i l -> Naturals l -> Naturals n
pattern NatRec n z k r s = FFNatRec n z (FFPatternRec k r) s

{-# COMPLETE Var, Zero, Suc, NatRec #-}

-- | The numeral @suc^k zero@.
numeral :: Int -> Naturals n
numeral k = iterate Suc Zero !! k

-- | Semantic values of naturals.
type Value = NbE.Value FFPattern TermSig

-- | One elimination rule. @natrec@ evaluates its scrutinee and recurses on
-- the value: at @zero@ it evaluates the zero branch, at @suc p@ it enters
-- the @suc@ branch under the environment extended with @p@ and with the
-- recursive result. Recursion on values with a stuck case for a neutral
-- scrutinee follows Abel ("Normalization by Evaluation: Dependent Types and
-- Impredicativity", 2013, Figure 3.2). The evaluation order does not: Abel's
-- rule is call-by-value and computes the recursive call first, whereas here
-- @recurse p@ is a thunk in the environment, computed only if the branch
-- uses @r@ and shared by every lookup. On anything else the recursion is
-- suspended with the scrutinee and the zero branch evaluated, so readback
-- normalises under the two names of the @suc@ branch. The zero branch is
-- evaluated at most once across the whole recursion. @zero@ and @suc@ fall
-- through to the default.
instance Eval FFPattern TermSig where
  evalSig scope env = \case
    NatRecSig n z (ScopedAST (FFPatternRec k r) s) ->
      case assertDistinct (FFPatternRec k r) of
        Distinct ->
          let zeroCase = eval scope env z
              recurse m = NbE.eliminate m $ \case
                NbE.VNode ZeroSig    -> zeroCase
                NbE.VNode (SucSig p) -> eval scope (addSubst (addSubst env k p) r (recurse p)) s
                NbE.Stuck m' -> NbE.vsuspended env (NatRecSig m' zeroCase (ScopedAST (FFPatternRec k r) s))
          in recurse (eval scope env n)
    node -> NbE.evalNode scope env node

-- | Weak-head normal form by substitution, for 'nfSubst'. The recursive
-- result is substituted as the unevaluated recursion on the predecessor. It
-- is not a reference for 'whnf', which also evaluates the zero branch of a
-- stuck recursion, a term position; the tests compare normal forms only.
whnfSubst :: Distinct n => Scope n -> Naturals n -> Naturals n
whnfSubst scope = \case
  NatRec n z k r s ->
    case whnfSubst scope n of
      Zero  -> whnfSubst scope z
      Suc p -> whnfSubst scope (substitute scope (stepSubst k p r (NatRec p z k r s)) s)
      n'    -> NatRec n' z k r s
  t -> t

-- | Normal form by substitution.
nfSubst :: Distinct n => Scope n -> Naturals n -> Naturals n
nfSubst scope = \case
  Suc n -> Suc (nfSubst scope n)
  NatRec n z k r s ->
    case whnfSubst scope n of
      Zero  -> nfSubst scope z
      Suc p -> nfSubst scope (substitute scope (stepSubst k p r (NatRec p z k r s)) s)
      n' ->
        case assertDistinct (FFPatternRec k r) of
          Distinct ->
            let scope' = extendScopePattern (FFPatternRec k r) scope
            in NatRec (nfSubst scope n') (nfSubst scope z) k r (nfSubst scope' s)
  t -> t

-- | The substitution that maps the two names of a @suc@ branch to the
-- predecessor and the recursive result.
stepSubst
  :: NameBinder n i -> Naturals n -> NameBinder i l -> Naturals n
  -> Substitution (AST FFPattern TermSig) l n
stepSubst k p r rec = addSubst (addSubst identitySubst k p) r rec
