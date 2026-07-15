{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

module LambdaPi where

import Control.DeepSeq (NFData)
import Data.Bifunctor.TH (deriveBifunctor)
import GHC.Generics (Generic)

import FreeFoil.NbE
    ( S(VoidS),
      Distinct,
      Scope,
      AST(..),
      NameBinder,
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
      quote' 
    )


data LambdaPiF scope term
  = AppF term term
  | LamF scope
  | PiF term scope
  deriving (Eq, Show, Functor, NFData, Generic)
deriveBifunctor ''LambdaPiF

type LambdaPi n = AST NameBinder LambdaPiF n

pattern App :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern App fun arg = Node (AppF fun arg)

pattern Lam :: NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Lam binder body = Node (LamF (ScopedAST binder body))

{-# COMPLETE Var, App, Lam #-}

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
type ValueF = Closure NameBinder LambdaPiF

eval :: (Distinct o, Distinct i) => Scope o -> Substitution ValueF i o -> LambdaPi i -> ValueF o
eval scope env = \case
  Var x -> lookupSubst env x
  App f x ->
    let fun = eval scope env f
        arg = eval scope env x
      in case fun of
        Closure env' (LamF (ScopedAST binder body)) ->
          case assertDistinct binder of
            Distinct ->
              let env'' = addSubst env' binder arg
              in eval scope env'' body
        fun' -> Closure identitySubst (AppF fun' arg)
  Lam binder body ->
    Closure env (LamF (ScopedAST binder body))


-- | Normal form
-- >>> Free.nf emptyScope (fromString "(λs. λz. s (s (s z))) (λs. λz. s (s z)) (λx. x) (λy. λz. y)")
-- λ x0 . λ x1 . x0
-- >>> Free.nf emptyScope (fromString "let x = (λx. (x,(x,x))) in (x x)")
-- (λ x0 . (x0, (x0, x0)), (λ x0 . (x0, (x0, x0)), λ x0 . (x0, (x0, x0))))
-- >>> Free.nf emptyScope (fromString "(λx. (x,(x,x)))")
-- λ x0 . (x0, (x0, x0))
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
