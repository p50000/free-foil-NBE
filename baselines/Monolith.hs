{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
-- The Eval instance is an orphan on purpose: it belongs with the language's
-- dynamics.
{-# OPTIONS_GHC -Wno-orphans #-}
-- | The monolithic demonstration language: functions, pairs and natural
-- numbers in one signature, written the way a language is written without
-- fragments, for comparison with "Fragments.Combined", which composes the
-- same language from "Fragments.Lambda", "Fragments.Pairs" and
-- "Fragments.Naturals". The three rules are those of "LambdaPi" and of
-- Renata Shakirova's "Pairs" and "Naturals". The syntax is generated in
-- "Monolith.Generated"; this module adds pattern synonyms over it and the
-- 'Eval' instance. The composed language is its reference normaliser in the
-- tests, and it is theirs.
--
-- A pattern binds one name or two, for every binder, so a lambda over a pair
-- of names or a @split@ over one name is syntactically possible; the rules
-- reject them.
module Monolith
  ( Monolith
  , FFPattern (..)
  , TermSig (..)
  , pattern Var
  , pattern Lam
  , pattern App
  , pattern Pi
  , pattern Pair
  , pattern Fst
  , pattern Snd
  , pattern Split
  , pattern Zero
  , pattern Suc
  , pattern NatRec
  , numeral
  , Value
  , eval
  , nf
  , whnf
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import FreeFoil.NbE (Eval (..), eval, nf, whnf)
import qualified FreeFoil.NbE as NbE

import Monolith.Generated

-- | Terms of the monolithic language in scope @n@.
type Monolith n = FFTerm n

-- | Semantic values of the monolithic language.
type Value = NbE.Value FFPattern TermSig

{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> Monolith n -> Monolith n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o -> Substitution Value i o -> Monolith i -> Value o #-}
{-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> Value n -> Monolith n #-}

pattern Lam :: FFPattern n l -> Monolith l -> Monolith n
pattern Lam pat body = FFLam pat body

pattern App :: Monolith n -> Monolith n -> Monolith n
pattern App fun arg = FFApp fun arg

pattern Pi :: Monolith n -> FFPattern n l -> Monolith l -> Monolith n
pattern Pi dom pat cod = FFPi dom pat cod

pattern Pair :: Monolith n -> Monolith n -> Monolith n
pattern Pair a b = FFPair a b

pattern Fst :: Monolith n -> Monolith n
pattern Fst p = FFFst p

pattern Snd :: Monolith n -> Monolith n
pattern Snd p = FFSnd p

pattern Split :: Monolith n -> FFPattern n l -> Monolith l -> Monolith n
pattern Split p pat body = FFSplit p pat body

pattern Zero :: Monolith n
pattern Zero = FFZero

pattern Suc :: Monolith n -> Monolith n
pattern Suc t = FFSuc t

pattern NatRec :: Monolith n -> Monolith n -> FFPattern n l -> Monolith l -> Monolith n
pattern NatRec n z pat s = FFNatRec n z pat s

{-# COMPLETE Var, Lam, App, Pi, Pair, Fst, Snd, Split, Zero, Suc, NatRec #-}

-- | The numeral of a natural number.
numeral :: Int -> Monolith n
numeral k = iterate Suc Zero !! k

-- | The three elimination rules, side by side, each as in its standalone
-- language: β, the projections and @split@, and primitive recursion. A
-- binder of the wrong shape is an error.
instance Eval FFPattern TermSig where
  evalSig scope env = \case
    AppSig fun arg ->
      case eval scope env fun of
        NbE.VSuspended env' (LamSig (ScopedAST (FFPatternVar binder) body)) ->
          case assertDistinct binder of
            Distinct -> eval scope (addSubst env' binder (eval scope env arg)) body
        NbE.VSuspended _ (LamSig (ScopedAST FFPatternPair {} _)) ->
          error "Monolith: a lambda binds one name"
        fun' -> NbE.VNode (AppSig fun' (eval scope env arg))
    FstSig p ->
      case eval scope env p of
        NbE.VNode (PairSig a _) -> a
        p'                     -> NbE.VNode (FstSig p')
    SndSig p ->
      case eval scope env p of
        NbE.VNode (PairSig _ b) -> b
        p'                     -> NbE.VNode (SndSig p')
    SplitSig p (ScopedAST (FFPatternPair x y) body) ->
      case eval scope env p of
        NbE.VNode (PairSig a b) ->
          case assertDistinct (FFPatternPair x y) of
            Distinct -> eval scope (addSubst (addSubst env x a) y b) body
        p' -> NbE.VSuspended env (SplitSig p' (ScopedAST (FFPatternPair x y) body))
    SplitSig _ (ScopedAST FFPatternVar {} _) ->
      error "Monolith: split binds two names"
    NatRecSig n z (ScopedAST (FFPatternPair k r) s) ->
      case assertDistinct (FFPatternPair k r) of
        Distinct ->
          let zeroCase = eval scope env z
              recurse m = case m of
                NbE.VNode ZeroSig    -> zeroCase
                NbE.VNode (SucSig p) -> eval scope (addSubst (addSubst env k p) r (recurse p)) s
                m' -> NbE.VSuspended env (NatRecSig m' zeroCase (ScopedAST (FFPatternPair k r) s))
          in recurse (eval scope env n)
    NatRecSig _ _ (ScopedAST FFPatternVar {} _) ->
      error "Monolith: the suc branch of natrec binds two names"
    node -> NbE.evalNode (eval scope) env node
