{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
-- The Show instance of a synonym over library types.
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Dependent functions and pairs over a universe, with a unit type: a
-- language whose context holds types. Its terms are elaborated (see
-- "DependentTypes.Elaborate"). Every node carries its type as free-foil's
-- annotation ('TypeAnn'), except the universe, whose type is itself.
--
-- η for functions and the unit type goes by types. In a context of types
-- ('HasTypes'), readback turns a neutral @f : (x : A) -> B@ into
-- @\\(x : A). f x@, and a neutral of type @Unit@ into @tt@. η for pairs goes
-- by shape ('NbE.etaMatchWith'), so @p@ is a normal form, convertible with
-- @(first p, second p)@.
--
-- The grammar follows the monolithic language's, with the projections
-- named as in Rzk, and the modules follow Renata Shakirova's pairs language.
module DependentTypes
  ( -- * Terms
    Sig
  , TypeAnn (..)
  , Elaborated
  , Raw
  , Value
  , TypeValue
  , unannotated
  , fullyAnnotated
  , universe
  , unitType
    -- * Contexts of types
  , HasTypes (..)
  , Typing
  , emptyTyping
  , typeOf
  , codomainAt
    -- * Normalisation
  , eval
  , nf
  , whnf
  , convertible
  ) where

import Control.Monad.Foil
import Control.Monad.Free.Foil
import Control.Monad.Free.Foil.Annotated (AnnSig (..))
import Data.Bifoldable (bifold)
import Data.Foldable (fold)
import Data.Functor.Const (Const (..))
import Data.Bifunctor (bimap)
import Data.Monoid (All (..))
import Data.ZipMatchK (ZipMatchFoldK (..), ZipMatchK (..))
import Data.ZipMatchK.Mappings (Mappings (..))
import FreeFoil.NbE (Eval (..), Extend (..), HasDefinitions (..), HasHeads (..))
import Generics.Kind.TH (deriveGenericK)
import qualified FreeFoil.NbE as NbE
import qualified FreeFoil.NbE.Conversion as Conv

import DependentTypes.Generated (FFPattern (..), FFTerm, TermSig (..))

-- | The annotation of an elaborated node: its type. Only the universe has
-- none, since its type is itself.
data TypeAnn ty
  = HasType ty
  | IsUniverse
  deriving (Functor, Foldable, Traversable)

deriveGenericK ''TypeAnn

-- | Matching ignores the annotations, as free-foil's documentation of
-- 'AnnSig' advises for types: conversion and α-equivalence compare terms,
-- and only refinement reads their types. A match always succeeds, and its
-- annotation is a thunk that the folds of a match, which skip annotations,
-- never force.
instance ZipMatchK TypeAnn where
  zipMatchWithK (f :^: M0) l r = Just $ case (l, r) of
    (HasType a, HasType b) | Just c <- f a b -> HasType c
    (IsUniverse, IsUniverse) -> IsUniverse
    _ -> error "DependentTypes: impossible: the paired types of a match are never used"

instance ZipMatchFoldK TypeAnn where
  zipMatchFoldK _ _ _ = Just mempty

-- | The signature of elaborated terms.
type Sig = AnnSig TypeAnn TermSig

-- | Elaborated terms in scope @n@.
type Elaborated n = AST FFPattern Sig n

-- | Terms as parsed, before elaboration.
type Raw n = FFTerm n

-- | Semantic values.
type Value = NbE.Value FFPattern Sig

-- | Values that are types.
type TypeValue = Value

-- | A term without its annotations.
unannotated :: Elaborated n -> Raw n
unannotated = hoistAST (\(AnnSig _ node) -> node)

-- | Whether every node but the universe carries its type, also inside the
-- annotations, as elaboration and normalisation produce them.
fullyAnnotated :: Elaborated n -> Bool
fullyAnnotated = getAll . getConst . foldAST (\_ -> mempty) (\_ (Const body) -> Const body) node
  where
    node :: forall (m :: S). AnnSig TypeAnn TermSig (Const All m) (Const All m) -> Const All m
    node (AnnSig ann t) = Const (All (fits ann t)) <> fold ann <> bifold t
    fits :: TypeAnn a -> TermSig b c -> Bool
    fits IsUniverse UniverseSig = True
    fits IsUniverse _           = False
    fits (HasType _) UniverseSig = False
    fits (HasType _) _           = True

-- | Terms print without their annotations.
instance Show (AST FFPattern Sig n) where
  show = show . unannotated

-- | The universe, whose type is itself.
universe :: TypeValue n
universe = NbE.VNode (AnnSig IsUniverse UniverseSig)

-- | The unit type.
unitType :: TypeValue n
unitType = NbE.VNode (AnnSig (HasType universe) UnitSig)

-- | The type in an annotation.
annotatedType :: TypeAnn (TypeValue n) -> TypeValue n
{-# INLINE annotatedType #-}
annotatedType = \case
  HasType ty -> ty
  IsUniverse -> universe

-- * Contexts of types

-- | What the language needs of a context: the type of every name in scope.
class HasTypes ctx where
  -- | The context under a binder of one name of a type.
  assume :: DExt n l => NameBinder n l -> TypeValue n -> ctx n -> ctx l
  -- | The type of a name.
  typeOfName :: ctx n -> Name n -> TypeValue n

-- | A type for every name in scope.
newtype Typing n = Typing (NameMap n (TypeValue n))

-- | The context of the empty scope.
emptyTyping :: Typing VoidS
emptyTyping = Typing emptyNameMap

-- | The type of a name.
typeOf :: Name n -> Typing n -> TypeValue n
typeOf x (Typing types) = lookupName x types

instance HasTypes Typing where
  assume x ty (Typing types) = Typing (addNameBinder x (sink ty) (sink1 types))
  typeOfName (Typing types) x = lookupName x types

instance HasDefinitions Typing FFPattern Sig where
  contextDefinition _ _ = NbE.VVar

-- * Rules

{-# SPECIALIZE NbE.nf :: Distinct n => Scope n -> Typing n -> Elaborated n -> Elaborated n #-}
{-# SPECIALIZE NbE.eval ::
      (Distinct o, Distinct i) =>
      Scope o -> Typing o -> Substitution Value i o -> Elaborated i -> Value o #-}
{-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> Typing n -> Value n -> Elaborated n #-}
{-# SPECIALIZE Conv.conv :: Distinct n => Scope n -> Typing n -> Value n -> Value n -> Bool #-}

-- | The heads are the function of an application and the pair of a
-- projection, which refinement leaves alone.
instance HasHeads TermSig where
  {-# INLINE headsWith #-}
  headsWith hd other = \case
    AppSig fun arg -> AppSig (hd fun) (other arg)
    FirstSig p     -> FirstSig (hd p)
    SecondSig p    -> SecondSig (hd p)
    node           -> bimap id other node

-- | β for functions and projections, the types of bound names, and η.
instance (HasTypes ctx, HasDefinitions ctx FFPattern Sig) => Eval ctx FFPattern Sig where
  {-# INLINABLE evalSig #-}
  evalSig scope ctx env (AnnSig ann node) = case node of
    AppSig fun arg ->
      appValue (fmap (NbE.eval scope ctx env) ann) scope ctx (NbE.eval scope ctx env fun) (NbE.eval scope ctx env arg)
    FirstSig p  -> firstValue (fmap (NbE.eval scope ctx env) ann) (NbE.eval scope ctx env p)
    SecondSig p -> secondValue (fmap (NbE.eval scope ctx env) ann) (NbE.eval scope ctx env p)
    _ -> NbE.evalNode scope ctx env (AnnSig ann node)

  {-# INLINE etaMatchWith #-}
  etaMatchWith _ term (AnnSig ann node) = case (ann, node) of
    (HasType ty, PairSig a b) -> Just $ AnnSig
      (HasType (term ty (NbE.EtaTerm (\_ c -> typeOfValue c))))
      (PairSig (term a (NbE.EtaTerm firstOf)) (term b (NbE.EtaTerm secondOf)))
    _ -> Nothing

  {-# INLINE extendScopedWith #-}
  extendScopedWith scoped term (AnnSig ann node) = AnnSig (fmap term ann) $ case node of
    LamSig dom body   -> LamSig (term dom) (scoped body (assumeVar dom))
    PiSig dom body    -> PiSig (term dom) (scoped body (assumeVar dom))
    SigmaSig dom body -> SigmaSig (term dom) (scoped body (assumeVar dom))
    AppSig fun arg    -> AppSig (term fun) (term arg)
    FirstSig p        -> FirstSig (term p)
    SecondSig p       -> SecondSig (term p)
    PairSig a b       -> PairSig (term a) (term b)
    UniverseSig       -> UniverseSig
    UnitSig           -> UnitSig
    TTSig             -> TTSig

  {-# INLINABLE refineVar #-}
  refineVar scope ctx x = expandAt scope ctx (NbE.VVar x) (typeOfName ctx x)

  -- A node in a value is a neutral only if it is an eliminator.
  {-# INLINABLE refineSig #-}
  refineSig scope ctx value (AnnSig ann node) = case node of
    AppSig {}    -> expandAt scope ctx value (annotatedType ann)
    FirstSig {}  -> expandAt scope ctx value (annotatedType ann)
    SecondSig {} -> expandAt scope ctx value (annotatedType ann)
    _            -> value

-- | Apply a function value to an argument value: a suspended lambda is
-- entered under its environment extended with the argument, any other
-- function is a stuck application of the type in the annotation.
appValue ::
  (Eval ctx FFPattern Sig, Distinct n) =>
  TypeAnn (TypeValue n) -> Scope n -> ctx n -> Value n -> Value n -> Value n
{-# INLINE appValue #-}
appValue ann scope ctx fun arg = case fun of
  NbE.VSuspended env (AnnSig _ (LamSig _ (ScopedAST (FFPatternVar x) body))) ->
    case assertDistinct x of
      Distinct -> NbE.eval scope ctx (addSubst env x arg) body
  _ -> NbE.VNode (AnnSig ann (AppSig fun arg))

-- | The first component of a pair value. Any other value gives a stuck
-- projection of the type in the annotation.
firstValue :: TypeAnn (TypeValue n) -> Value n -> Value n
{-# INLINE firstValue #-}
firstValue ann p = case p of
  NbE.VNode (AnnSig _ (PairSig a _)) -> a
  _ -> NbE.VNode (AnnSig ann (FirstSig p))

-- | The second component of a pair value, like 'firstValue'.
secondValue :: TypeAnn (TypeValue n) -> Value n -> Value n
{-# INLINE secondValue #-}
secondValue ann p = case p of
  NbE.VNode (AnnSig _ (PairSig _ b)) -> b
  _ -> NbE.VNode (AnnSig ann (SecondSig p))

-- | The projections for η of pairs. They carry their types, so that they are
-- refined as well.
firstOf :: HasTypes ctx => Scope n -> ctx n -> Value n -> Value n
{-# INLINE firstOf #-}
firstOf _ ctx p = case typeOfValue ctx p of
  NbE.VSuspended _ (AnnSig _ (SigmaSig a _)) -> firstValue (HasType a) p
  _ -> notOfPairType

secondOf :: (Eval ctx FFPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> Value n -> Value n
{-# INLINE secondOf #-}
secondOf scope ctx p = case typeOfValue ctx p of
  NbE.VSuspended env (AnnSig _ (SigmaSig _ cod)) ->
    secondValue (HasType (codomainAt scope ctx env cod (firstOf scope ctx p))) p
  _ -> notOfPairType

-- | Impossible: conversion compares two values of one type, so the value
-- that η compares with a pair has the pair's type, which is a Σ.
notOfPairType :: a
notOfPairType = error "DependentTypes: impossible: η for a pair against a value whose type is not a Σ"

-- | The type of a value: of a variable from the context, of a node from its
-- annotation.
typeOfValue :: HasTypes ctx => ctx n -> Value n -> TypeValue n
{-# INLINE typeOfValue #-}
typeOfValue ctx = \case
  NbE.VVar x -> typeOfName ctx x
  NbE.VNode (AnnSig ann _) -> annotatedType ann
  NbE.VSuspended _ (AnnSig ann _) -> annotatedType ann

-- | The binder of one name of a type.
assumeVar :: HasTypes ctx => TypeValue n -> Extend ctx FFPattern Sig n
{-# INLINE assumeVar #-}
assumeVar ty = Extend $ \_ pat _ ctx -> case pat of
  FFPatternVar x -> assume x ty ctx

-- | The codomain of a Π or Σ type at a value, from the environment and the
-- codomain of the type's value.
codomainAt ::
  (Eval ctx FFPattern Sig, Distinct n, Distinct i) =>
  Scope n -> ctx n -> Substitution Value i n -> ScopedAST FFPattern Sig i -> Value n -> TypeValue n
{-# INLINE codomainAt #-}
codomainAt scope ctx env (ScopedAST (FFPatternVar b) cod) arg = case assertDistinct b of
  Distinct -> NbE.eval scope ctx (addSubst env b arg) cod

-- | η-expand a neutral at its type.
expandAt :: (Eval ctx FFPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> Value n -> TypeValue n -> Value n
{-# INLINE expandAt #-}
expandAt scope ctx value ty = case ty of
  NbE.VNode (AnnSig _ UnitSig) -> NbE.VNode (AnnSig (HasType unitType) TTSig)
  NbE.VSuspended env (AnnSig _ (PiSig dom cod)) -> expandFunction scope ctx value ty dom env cod
  _ -> value

-- | A neutral @f : (x : A) -> B@ as the value of @\\(x : A). f x@, whose
-- application is annotated with @B@. The value of @f@ sits in the
-- environment under a fresh name @g@. The type comes whole and in parts:
-- its domain, and the environment and codomain of its value.
expandFunction ::
  (Eval ctx FFPattern Sig, HasTypes ctx, Distinct n, Distinct i) =>
  Scope n -> ctx n -> Value n -> TypeValue n -> TypeValue n ->
  Substitution Value i n -> ScopedAST FFPattern Sig i -> Value n
{-# INLINE expandFunction #-}
expandFunction scope ctx fun ty dom env codomain =
  withFresh scope $ \g ->
    let scopeG = extendScope g scope
        ctxG = assume g ty ctx
    in withFresh scopeG $ \x ->
         let scopeX = extendScope x scopeG
             ctxX = assume x (sink dom) ctxG
             cod = NbE.quote scopeX ctxX (codomainAt scopeX ctxX (sink env) codomain (NbE.VVar (nameOf x)))
             body = Node (AnnSig (HasType cod) (AppSig (Var (sink (nameOf g))) (Var (nameOf x))))
         in NbE.VSuspended (addSubst identitySubst g fun)
              (AnnSig (HasType ty) (LamSig dom (ScopedAST (FFPatternVar x) body)))

-- * Normalisation

-- | Evaluation in a context of types.
eval :: (Distinct o, Distinct i) => Scope o -> Typing o -> Substitution Value i o -> Elaborated i -> Value o
{-# INLINE eval #-}
eval = NbE.eval

-- | Normal form in a context of types.
nf :: Distinct n => Scope n -> Typing n -> Elaborated n -> Elaborated n
{-# INLINE nf #-}
nf = NbE.nf

-- | Weak-head normal form in a context of types.
whnf :: Distinct n => Scope n -> Typing n -> Elaborated n -> Elaborated n
{-# INLINE whnf #-}
whnf = NbE.whnf

-- | Convertibility in a context of types.
convertible :: Distinct n => Scope n -> Typing n -> Elaborated n -> Elaborated n -> Bool
{-# INLINE convertible #-}
convertible = Conv.convertible
