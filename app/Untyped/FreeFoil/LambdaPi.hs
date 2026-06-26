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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

module LambdaPi where 

import Untyped.FreeFoil.Internal as FreeFoil


--- Impl of nf, whnf using generic sinking
data LambdaPiF scope term
  = AppF term term
  | LamF scope
  | PiF term scope
  deriving (Eq, Show, Functor, NFData, Generic)
deriveBifunctor ''LambdaPiF

type LambdaPi n = FreeFoil.AST LambdaPiF n

pattern App :: LambdaPi n -> LambdaPi n -> LambdaPi n
pattern App fun arg = Node (AppF fun arg)

pattern Lam :: NameBinder n l -> LambdaPi l -> LambdaPi n
pattern Lam binder body = Node (LamF (ScopedAST binder body))

{-# COMPLETE Var, App, Lam #-}

whnf :: FreeFoil.Distinct n => FreeFoil.Scope n -> LambdaPi n -> LambdaPi n
whnf scope = \case
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst = FreeFoil.addSubst FreeFoil.identitySubst binder arg
        in whnf scope (FreeFoil.substitute scope subst body)
      fun' -> App fun' arg
  t -> t

nf :: FreeFoil.Distinct n => FreeFoil.Scope n -> LambdaPi n -> LambdaPi n
nf scope = \case
  Lam binder body -> FreeFoil.unsafeAssertFresh binder \binder' ->
          let scope' = FreeFoil.extendScope binder' scope
        in Lam binder' (nf scope' body)
  App fun arg ->
    case whnf scope fun of
      Lam binder body ->
        let subst =  FreeFoil.addSubst FreeFoil.identitySubst binder arg
        in nf scope (substitute scope subst body)
      fun' -> App (nf scope fun') (nf scope arg)
  t -> t

nfd :: LambdaPi VoidS -> LambdaPi VoidS
nfd term = nf FreeFoil.emptyScope term

--- examples
two :: LambdaPi VoidS
two = FreeFoil.withFresh FreeFoil.emptyScope
  (\ s -> Lam s $ FreeFoil.withFresh (FreeFoil.extendScope s FreeFoil.emptyScope)
    (\ z -> Lam z (App (Var (FreeFoil.sink (FreeFoil.nameOf s)))
                        (App (Var (sink (nameOf s)))
                             (Var (nameOf z))))))

appTwo = App two two