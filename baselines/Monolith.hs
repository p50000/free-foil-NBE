{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- the Eval instance belongs with the rules
-- | The monolithic demonstration language: functions, pairs and natural
-- numbers in one signature, written the way a language is written without
-- fragments, for comparison with "Fragments.Combined", which composes the
-- same language from "Fragments.Lambda", "Fragments.Pairs" and
-- "Fragments.Naturals". The three rules are those of "LambdaPi",
-- "Pairs" and "Naturals". The syntax is generated in
-- "Monolith.Generated"; this module adds the 'Eval' instance.
--
-- A pattern binds one name or two, for every binder, so a lambda over a pair
-- of names or a @split@ over one name is syntactically possible; the rules
-- reject them.
module Monolith
  ( Monolith
  , Pattern (..)
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
import Data.Bifunctor (bimap)
import FreeFoil.NbE (Eval (..), HasDefinitions, HasHeads (..))
import qualified FreeFoil.NbE as NbE
import qualified FreeFoil.NbE.Conversion as Conv

import Monolith.Generated

-- | Terms of the monolithic language in scope @n@.
type Monolith n = Term n

-- | Semantic values of the monolithic language.
type Value = NbE.Value Pattern TermSig

{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> NbE.NoContext n -> Monolith n -> Monolith n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o -> NbE.NoContext o -> Substitution Value i o -> Monolith i -> Value o #-}
{-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> NbE.NoContext n -> Value n -> Monolith n #-}
{-# SPECIALIZE Conv.conv :: Distinct n => Scope n -> NbE.NoContext n -> Value n -> Value n -> Bool #-}
{-# SPECIALIZE Conv.convertible :: Distinct n => Scope n -> NbE.NoContext n -> Monolith n -> Monolith n -> Bool #-}

-- | Evaluation in a scope, with no other context.
eval :: (Distinct o, Distinct i) => Scope o -> Substitution Value i o -> Monolith i -> Value o
{-# INLINE eval #-}
eval scope = NbE.eval scope NbE.NoContext

-- | Normal form in a scope, with no other context.
nf :: Distinct n => Scope n -> Monolith n -> Monolith n
{-# INLINE nf #-}
nf scope = NbE.nf scope NbE.NoContext

-- | Weak-head normal form in a scope, with no other context.
whnf :: Distinct n => Scope n -> Monolith n -> Monolith n
{-# INLINE whnf #-}
whnf scope = NbE.whnf scope NbE.NoContext

-- | The numeral of a natural number.
numeral :: Int -> Monolith n
numeral k = iterate Suc Zero !! k

-- | The heads: the function of an application, the pair of a projection and
-- of @split@, and the scrutinee of @natrec@.
instance HasHeads TermSig where
  {-# INLINE headsWith #-}
  headsWith hd other = \case
    AppSig fun arg  -> AppSig (hd fun) (other arg)
    FstSig p        -> FstSig (hd p)
    SndSig p        -> SndSig (hd p)
    SplitSig p body -> SplitSig (hd p) body
    NatRecSig n z s -> NatRecSig (hd n) (other z) s
    node            -> bimap id other node

-- | The three elimination rules, side by side, each as in its standalone
-- language: β, the projections and @split@, and primitive recursion. A
-- binder of the wrong shape is an error.
instance (Sinkable ctx, HasDefinitions ctx Pattern TermSig) => Eval ctx Pattern TermSig where
  {-# INLINABLE evalSig #-}
  evalSig scope ctx env = \case
    AppSig fun arg ->
      let arg' = NbE.eval scope ctx env arg
      in NbE.eliminate (NbE.eval scope ctx env fun) $ \case
        NbE.VSuspended env' (LamSig (ScopedAST (PatternVar binder) body)) ->
          case assertDistinct binder of
            Distinct -> NbE.eval scope ctx (addSubst env' binder arg') body
        NbE.VSuspended _ (LamSig (ScopedAST PatternPair {} _)) ->
          error "Monolith: a lambda binds one name"
        NbE.Stuck fun' -> NbE.vnode (AppSig fun' arg')
    FstSig p ->
      NbE.eliminate (NbE.eval scope ctx env p) $ \case
        NbE.VNode (PairSig a _) -> a
        NbE.Stuck p'            -> NbE.vnode (FstSig p')
    SndSig p ->
      NbE.eliminate (NbE.eval scope ctx env p) $ \case
        NbE.VNode (PairSig _ b) -> b
        NbE.Stuck p'            -> NbE.vnode (SndSig p')
    SplitSig p (ScopedAST (PatternPair x y) body) ->
      NbE.eliminate (NbE.eval scope ctx env p) $ \case
        NbE.VNode (PairSig a b) ->
          case assertDistinct (PatternPair x y) of
            Distinct -> NbE.eval scope ctx (addSubst (addSubst env x a) y b) body
        NbE.Stuck p' -> NbE.vsuspended env (SplitSig p' (ScopedAST (PatternPair x y) body))
    SplitSig _ (ScopedAST PatternVar {} _) ->
      error "Monolith: split binds two names"
    NatRecSig n z (ScopedAST (PatternPair k r) s) ->
      case assertDistinct (PatternPair k r) of
        Distinct ->
          let zeroCase = NbE.eval scope ctx env z
              recurse m = NbE.eliminate m $ \case
                NbE.VNode ZeroSig    -> zeroCase
                NbE.VNode (SucSig p) -> NbE.eval scope ctx (addSubst (addSubst env k p) r (recurse p)) s
                NbE.Stuck m' -> NbE.vsuspended env (NatRecSig m' zeroCase (ScopedAST (PatternPair k r) s))
          in recurse (NbE.eval scope ctx env n)
    NatRecSig _ _ (ScopedAST PatternVar {} _) ->
      error "Monolith: the suc branch of natrec binds two names"
    node -> NbE.evalNode scope ctx env node
