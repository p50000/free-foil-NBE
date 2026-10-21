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
-- | The pairs demonstration language: a pair former, the two projections and
-- @split@, whose pattern binds both components at once. There are no
-- functions and no constants, so every term is open. The syntax is generated
-- in "Pairs.Generated"; this module adds pattern synonyms over it, the 'Eval'
-- instance, and a substitution-based reference normaliser. Example terms are
-- in "Pairs.Examples".
--
-- New against the other languages is a pattern that binds two names:
-- readback refreshes both at once, and conversion checking pairs them by
-- position.
module Pairs
  ( Pairs
  , pattern Var
  , pattern Pair
  , pattern Fst
  , pattern Snd
  , pattern Split
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

import Pairs.Generated
  ( FFPattern (FFPatternPair)
  , FFTerm
  , TermSig (FstSig, PairSig, SndSig, SplitSig)
  , pattern FFFst
  , pattern FFPair
  , pattern FFSnd
  , pattern FFSplit
  )

-- | Scope-safe pairs terms in scope @n@.
type Pairs n = FFTerm n

-- Specialise the generic loop to this signature, as in "LambdaPi".
{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> Pairs n -> Pairs n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o ->
      Substitution (NbE.Value FFPattern TermSig) i o ->
      Pairs i ->
      NbE.Value FFPattern TermSig o #-}
{-# SPECIALIZE NbE.quote ::
      Distinct n => Scope n -> NbE.Value FFPattern TermSig n -> Pairs n #-}
{-# SPECIALIZE Conv.conv :: Distinct n => Scope n -> Value n -> Value n -> Bool #-}
{-# SPECIALIZE Conv.convertible :: Distinct n => Scope n -> Pairs n -> Pairs n -> Bool #-}

-- | @(a, b)@.
pattern Pair :: Pairs n -> Pairs n -> Pairs n
pattern Pair a b = FFPair a b

-- | @fst p@.
pattern Fst :: Pairs n -> Pairs n
pattern Fst p = FFFst p

-- | @snd p@.
pattern Snd :: Pairs n -> Pairs n
pattern Snd p = FFSnd p

-- | @split p as (x, y) in body@; @y@ is bound in the scope of @x@.
pattern Split :: Pairs n -> NameBinder n i -> NameBinder i l -> Pairs l -> Pairs n
pattern Split p x y body = FFSplit p (FFPatternPair x y) body

{-# COMPLETE Var, Pair, Fst, Snd, Split #-}

-- | Semantic values of pairs.
type Value = NbE.Value FFPattern TermSig

-- | Three elimination rules. A projection of a pair value selects a
-- component, and is stuck on anything else. @split@ of a pair value enters
-- its body under the environment extended with both components, as β
-- enters a lambda body; on anything else it is suspended with its scrutinee
-- evaluated, so readback normalises under its two names. A pair falls
-- through to the default and becomes a 'NbE.VNode' whose components are
-- lazy values.
instance Eval FFPattern TermSig where
  evalSig scope env = \case
    FstSig p ->
      NbE.eliminate (eval scope env p) $ \case
        NbE.VNode (PairSig a _) -> a
        NbE.Stuck p'                     -> NbE.vnode (FstSig p')
    SndSig p ->
      NbE.eliminate (eval scope env p) $ \case
        NbE.VNode (PairSig _ b) -> b
        NbE.Stuck p'                     -> NbE.vnode (SndSig p')
    SplitSig p (ScopedAST (FFPatternPair x y) body) ->
      NbE.eliminate (eval scope env p) $ \case
        NbE.VNode (PairSig a b) ->
          case assertDistinct (FFPatternPair x y) of
            Distinct -> eval scope (addSubst (addSubst env x a) y b) body
        NbE.Stuck p' -> NbE.vsuspended env (SplitSig p' (ScopedAST (FFPatternPair x y) body))
    node -> NbE.evalNode scope env node

-- | Weak-head normal form by substitution, the reference for the tests.
whnfSubst :: Distinct n => Scope n -> Pairs n -> Pairs n
whnfSubst scope = \case
  Fst p ->
    case whnfSubst scope p of
      Pair a _ -> whnfSubst scope a
      p'       -> Fst p'
  Snd p ->
    case whnfSubst scope p of
      Pair _ b -> whnfSubst scope b
      p'       -> Snd p'
  Split p x y body ->
    case whnfSubst scope p of
      Pair a b -> whnfSubst scope (substitute scope (bothSubst x a y b) body)
      p'       -> Split p' x y body
  t -> t

-- | Normal form by substitution.
nfSubst :: Distinct n => Scope n -> Pairs n -> Pairs n
nfSubst scope = \case
  Pair a b -> Pair (nfSubst scope a) (nfSubst scope b)
  Fst p ->
    case whnfSubst scope p of
      Pair a _ -> nfSubst scope a
      p'       -> Fst (nfSubst scope p')
  Snd p ->
    case whnfSubst scope p of
      Pair _ b -> nfSubst scope b
      p'       -> Snd (nfSubst scope p')
  Split p x y body ->
    case whnfSubst scope p of
      Pair a b -> nfSubst scope (substitute scope (bothSubst x a y b) body)
      p' ->
        case assertDistinct (FFPatternPair x y) of
          Distinct ->
            let scope' = extendScopePattern (FFPatternPair x y) scope
            in Split (nfSubst scope p') x y (nfSubst scope' body)
  t -> t

-- | The substitution that maps the two names of a @split@ pattern to the
-- components of its scrutinee.
bothSubst
  :: NameBinder n i -> Pairs n -> NameBinder i l -> Pairs n
  -> Substitution (AST FFPattern TermSig) l n
bothSubst x a = addSubst (addSubst identitySubst x a)
