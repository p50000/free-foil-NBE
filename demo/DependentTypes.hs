{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
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
-- | Dependent functions and pairs over a cumulative hierarchy of universes
-- @U 0@, @U 1@, …, with a unit type and an identity type: a language whose
-- context holds types. Its terms are elaborated (see
-- "DependentTypes.Elaborate"). Every node carries its type as free-foil's
-- annotation ('TypeAnn'), except a universe, whose type is the next
-- universe. The binder of a λ is a pattern, a variable or a pair of
-- patterns, and carries the type of every name it binds and of every pair
-- ('TypedPattern'). A pair pattern stands for the pair of its components
-- ('patternValue'), and bound to a value binds them to its projections
-- ('bindPattern'). Conversion compares a λ over a pair pattern with a λ over
-- a variable through these two ('NbE.binderValue', 'NbE.bindValue'), and
-- moves the types of a binder under the environment when it enters one
-- ('NbE.evalBinder').
--
-- Conversion checks subtyping when the context says so ('Variance', as in
-- Rzk): @U i@ is a subtype of @U j@ for @i ≤ j@, a Π is contravariant in its
-- domain and covariant in its codomain, a Σ is covariant in both, and every
-- other position is compared invariantly ('NbE.relateWith'). Under the binder
-- of a Π or Σ, the bound name has the smaller of the two domains. This is the
-- cumulativity of Rocq's kernel (@ccnv@ in @kernel/conversion.ml@), except
-- that Rocq's Π is invariant in its domain, whereas here it is
-- contravariant, as for Rzk's shape-indexed functions.
--
-- η for functions and pairs goes by shape ('NbE.etaMatchWith'): conversion
-- compares a λ or a pair with another value through application or the
-- projections, so @f@ and @p@ are normal forms, convertible with
-- @\\(x : A). f x@ and @(first p, second p)@. Shape cannot relate two
-- different neutrals, which differ unless their type is a singleton: @Unit@,
-- a Π into a singleton, or a Σ of two. A type value records whether it is a
-- singleton ('IsSingletonType'), and in a context of types ('HasTypes')
-- readback and conversion turn a neutral of a singleton type into that
-- type's one value ('NbE.refineVar', 'NbE.refineSig'), such as @tt@ or
-- @\\(x : A). tt@.
--
-- η by shape is that of Abel and Coquand ("Untyped algorithmic equality for
-- Martin-Löf's logical framework with surjective pairs", 2007), who note that
-- it does not decide η for the unit type. Recognising singleton types follows
-- Agda (@isSingletonRecord@ in @Agda.TypeChecking.Records@, used when its
-- conversion compares two neutrals) and Kovács ("Eta conversion for the unit
-- type (is still not that simple)", WITS 2025), where neutrals carry the
-- lazily computed relevance of their types.
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
  , TypedPattern (..)
  , untypedPattern
  , unannotated
  , fullyAnnotated
  , universe
  , unitType
  , typeOfNode
  , typeOfValue
  , typeAnnotation
  , isSingletonType
    -- * Contexts of types
  , HasTypes (..)
  , Variance (..)
  , Typing
  , emptyTyping
  , typeOf
  , define
  , withUnfolding
  , Unfolding (..)
    -- * Binders
  , patternValue
  , bindPattern
  , codomainAt
    -- * Normalisation
  , eval
  , nf
  , whnf
  , convertible
  , isSubtype
  ) where

import Control.Monad.Foil
import Control.Monad.Foil.Internal (RenamingsK (..))
import Data.Coerce (coerce)
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
import FreeFoil.NbE.Definitions (Unfolding (..))

import DependentTypes.Generated (FFPattern (..), FFTerm, TermSig (..))

-- | The annotation of an elaborated node: its type, and for a type whether it
-- is a singleton. Only a universe has no type, since its type is the next
-- universe.
data TypeAnn ty
  = HasType ty
    -- ^ The type of a term, or the universe of a type that is not a
    -- singleton.
  | IsSingletonType ty
    -- ^ A singleton type, with its universe: @Unit@, a Π into a singleton,
    -- or a Σ of two.
  | IsUniverse
    -- ^ A universe @U i@, whose type @U (i + 1)@ is read from the node.
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
    (IsSingletonType a, IsSingletonType b) | Just c <- f a b -> IsSingletonType c
    (IsUniverse, IsUniverse) -> IsUniverse
    _ -> error "DependentTypes: impossible: the paired types of a match are never used"

instance ZipMatchFoldK TypeAnn where
  zipMatchFoldK _ _ _ = Just mempty

-- | The signature of elaborated terms.
type Sig = AnnSig TypeAnn TermSig

-- | Elaborated terms in scope @n@.
type Elaborated n = AST TypedPattern Sig n

-- | The binder of an elaborated term: a variable with its type, or a pair of
-- binders with its Σ type. Each type is in the scope before its binder, so
-- the type of the second component of a pair may mention the first.
data TypedPattern (n :: S) (l :: S) where
  TypedVar  :: NameBinder n l -> Elaborated n -> TypedPattern n l
  TypedPair :: Elaborated n -> TypedPattern n i -> TypedPattern i l -> TypedPattern n l

-- | The binder without its types.
untypedPattern :: TypedPattern n l -> FFPattern n l
untypedPattern = \case
  TypedVar x _    -> FFPatternVar x
  TypedPair _ l r -> FFPatternPair (untypedPattern l) (untypedPattern r)

-- | A refreshed binder renames the types after it, as free-foil's
-- telescopes do ('transportPayload').
instance CoSinkable TypedPattern where
  coSinkabilityProof rename (TypedVar x ty) cont =
    coSinkabilityProof rename x $ \rename' x' -> cont rename' (TypedVar x' (sinkabilityProof rename ty))
  coSinkabilityProof rename (TypedPair ty l r) cont =
    coSinkabilityProof rename l $ \renameL l' ->
      coSinkabilityProof renameL r $ \renameR r' ->
        cont renameR (TypedPair (sinkabilityProof rename ty) l' r')

  withPattern
    :: forall f o n l r. Distinct o
    => (forall x y z r'. Distinct z
          => Scope z
          -> NameBinder x y
          -> (forall z'. DExt z z' => f x y z z' -> NameBinder z z' -> r')
          -> r')
    -> (forall x z z'. DExt z z' => f x x z z')
    -> (forall x y y' z z' z''. (DExt z z', DExt z' z'')
          => f x y z z' -> f y y' z' z'' -> f x y' z z'')
    -> Scope o
    -> TypedPattern n l
    -> (forall o'. DExt o o' => f n l o o' -> TypedPattern o o' -> Scope o' -> r)
    -> r
  withPattern withBinder _unit comp scope0 pat0 cont0 =
    go verbatimTransport scope0 pat0 (\f pat' scope' _ -> cont0 f pat' scope')
    where
      go :: forall n' l' o' r'. Distinct o'
         => PatternTransport n' o' -> Scope o' -> TypedPattern n' l'
         -> (forall o''. DExt o' o'' => f n' l' o' o'' -> TypedPattern o' o'' -> Scope o'' -> PatternTransport l' o'' -> r')
         -> r'
      go transport scope (TypedVar x ty) cont =
        withBinder scope x $ \fx x' ->
          cont fx (TypedVar x' (transportPayload scope transport ty)) (extendScope x' scope)
            (transportUnderBinder transport x x')
      go transport scope (TypedPair ty l r) cont =
        go transport scope l $ \fl l' scopeL transportL ->
          go transportL scopeL r $ \fr r' scopeR transportR ->
            cont (comp fl fr) (TypedPair (transportPayload scope transport ty) l' r') scopeR transportR

-- | Renaming the outer scope renames the types, as 'coSinkabilityProof'
-- does. An index that the renaming skips keeps its names.
instance SinkableK TypedPattern where
  sinkabilityProofK renames pat cont = case renames of
    RCons rename (RCons _ RNil) ->
      coSinkabilityProof rename pat $ \rename' pat' -> cont (RCons rename (RCons rename' RNil)) pat'
    RCons rename (RSkip RNil) ->
      coSinkabilityProof rename pat $ \rename' pat' -> cont (RCons rename (RCons rename' RNil)) pat'
    RSkip (RCons _ RNil) ->
      coSinkabilityProof id pat $ \rename' pat' -> cont (RCons id (RCons rename' RNil)) pat'
    RSkip (RSkip RNil) ->
      coSinkabilityProof id pat $ \rename' pat' -> cont (RCons id (RCons rename' RNil)) pat'

-- | Two binders unify by their shape, as matching ignores types.
instance UnifiablePattern TypedPattern where
  unifyPatterns l r = coerce (unifyPatterns (untypedPattern l) (untypedPattern r))

-- | Terms as parsed, before elaboration.
type Raw n = FFTerm n

-- | Semantic values.
type Value = NbE.Value TypedPattern Sig

-- | Values that are types.
type TypeValue = Value

-- | A term without its annotations.
unannotated :: Elaborated n -> Raw n
unannotated = \case
  Var x -> Var x
  Node (AnnSig _ node) -> Node (bimap (\(ScopedAST pat body) -> ScopedAST (untypedPattern pat) (unannotated body)) unannotated node)

-- | Whether every node but a universe carries its type, also inside the
-- annotations and the types of binders, as elaboration and normalisation
-- produce them.
fullyAnnotated :: Elaborated n -> Bool
fullyAnnotated = getAll . getConst . foldAST (\_ -> mempty) (\pat (Const body) -> Const (All (typesAnnotated pat) <> body)) node
  where
    typesAnnotated :: TypedPattern a b -> Bool
    typesAnnotated = \case
      TypedVar _ ty     -> fullyAnnotated ty
      TypedPair ty l r  -> fullyAnnotated ty && typesAnnotated l && typesAnnotated r
    node :: forall (m :: S). AnnSig TypeAnn TermSig (Const All m) (Const All m) -> Const All m
    node (AnnSig ann t) = Const (All (fits ann t)) <> fold ann <> bifold t
    fits :: TypeAnn a -> TermSig b c -> Bool
    fits IsUniverse UniverseSig {}       = True
    fits IsUniverse _                    = False
    fits (IsSingletonType _) UnitSig     = True
    fits (IsSingletonType _) PiSig {}    = True
    fits (IsSingletonType _) SigmaSig {} = True
    fits (IsSingletonType _) _           = False
    fits (HasType _) UniverseSig {}      = False
    fits (HasType _) UnitSig             = False
    fits (HasType _) _                   = True

-- | Terms print without their annotations.
instance Show (AST TypedPattern Sig n) where
  show = show . unannotated

-- | The universe of a level, whose type is the next universe.
universe :: Integer -> TypeValue n
universe i = NbE.vnode (AnnSig IsUniverse (UniverseSig i))

-- | The unit type, in the lowest universe.
unitType :: TypeValue n
unitType = NbE.vnode (AnnSig (IsSingletonType (universe 0)) UnitSig)

-- | The annotation of a type, given its universe and whether the type is a
-- singleton.
typeAnnotation :: ty -> Bool -> TypeAnn ty
{-# INLINE typeAnnotation #-}
typeAnnotation u singleton
  | singleton = IsSingletonType u
  | otherwise = HasType u

-- | Whether a type value is a singleton type, as its unfolded head says.
isSingletonType :: TypeValue n -> Bool
{-# INLINE isSingletonType #-}
isSingletonType ty = case NbE.force ty of
  NbE.VNode (AnnSig ann _) -> isSingletonAnn ann
  NbE.VSuspended _ (AnnSig ann _) -> isSingletonAnn ann
  _ -> False

-- | Whether the annotation of a type says that it is a singleton.
isSingletonAnn :: TypeAnn ty -> Bool
{-# INLINE isSingletonAnn #-}
isSingletonAnn = \case
  IsSingletonType _ -> True
  _ -> False

-- | The type of a node, from its annotation, or for a universe from its
-- level.
typeOfNode :: TypeAnn (TypeValue n) -> TermSig a b -> TypeValue n
{-# INLINE typeOfNode #-}
typeOfNode ann node = case ann of
  HasType ty -> ty
  IsSingletonType ty -> ty
  IsUniverse -> case node of
    UniverseSig i -> universe (i + 1)
    _ -> error "DependentTypes: impossible: a node annotated as a universe that is not one"

-- * Contexts of types

-- | What the language needs of a context: the type of every name in scope,
-- and the direction in which conversion compares types.
class HasTypes ctx where
  -- | The context under a binder of one name of a type.
  assume :: DExt n l => NameBinder n l -> TypeValue n -> ctx n -> ctx l
  -- | The type of a name.
  typeOfName :: ctx n -> Name n -> TypeValue n
  -- | The direction of the comparison.
  variance :: ctx n -> Variance
  -- | The context with another direction.
  withVariance :: Variance -> ctx n -> ctx n

-- | The direction in which conversion compares two types, as in Rzk: under
-- 'Covariant' the left one is a subtype of the right one, under
-- 'Contravariant' a supertype, and under 'Invariant' the two are
-- convertible.
data Variance = Covariant | Contravariant | Invariant
  deriving (Eq, Show)

-- | The direction of the domain of a Π.
opposite :: Variance -> Variance
opposite = \case
  Covariant     -> Contravariant
  Contravariant -> Covariant
  Invariant     -> Invariant

-- | An entry for every name in scope, the side of a defined name that
-- readback follows, and the direction of the comparison.
data Typing n = Typing
  { typingVariance  :: Variance
  , typingUnfolding :: Unfolding
  , typingEntries   :: NameMap n (Entry n)
  }

-- | What the context knows of a name: its type, and its value when it is
-- defined.
data Entry n = Entry
  { entryType  :: TypeValue n
  , entryValue :: Maybe (Value n)
  }

instance Sinkable Entry where
  sinkabilityProof rename (Entry ty value) =
    Entry (sinkabilityProof rename ty) (fmap (sinkabilityProof rename) value)

-- | The context of the empty scope, for conversion. Readback unfolds every
-- definition.
emptyTyping :: Typing VoidS
emptyTyping = Typing
  { typingVariance = Invariant
  , typingUnfolding = Unfolded
  , typingEntries = emptyNameMap
  }

-- | The type of a name.
typeOf :: Name n -> Typing n -> TypeValue n
typeOf x typing = entryType (lookupName x (typingEntries typing))

-- | The context under a binder whose name has an entry. The entries in
-- scope sink by coercion ('sink1').
enter :: DExt n l => NameBinder n l -> Entry n -> Typing n -> Typing l
enter x entry typing = typing { typingEntries = addNameBinder x (sink entry) (sink1 (typingEntries typing)) }

-- | The context under a binder whose name has a type and a value: a
-- definition. The name evaluates to a glued value, so readback and
-- conversion can keep it folded.
define :: DExt n l => NameBinder n l -> TypeValue n -> Value n -> Typing n -> Typing l
define x ty value = enter x (Entry ty (Just value))

-- | The same context, with readback following the given side of a defined
-- name.
withUnfolding :: Unfolding -> Typing n -> Typing n
withUnfolding side typing = typing { typingUnfolding = side }

instance HasTypes Typing where
  assume x ty = enter x (Entry ty Nothing)
  typeOfName typing x = entryType (lookupName x (typingEntries typing))
  variance = typingVariance
  withVariance v typing = typing { typingVariance = v }

-- | A defined name is glued to its value, any other name is a neutral.
instance HasDefinitions Typing TypedPattern Sig where
  contextDefinition _ typing x =
    case entryValue (lookupName x (typingEntries typing)) of
      Just value -> NbE.vglued x value
      Nothing    -> NbE.vvar x
  contextUnfolding _ typing folded unfolded = case typingUnfolding typing of
    Folded   -> folded
    Unfolded -> unfolded

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

-- | β for functions and projections, the types of bound names, singleton
-- types, and η.
instance (HasTypes ctx, HasDefinitions ctx TypedPattern Sig) => Eval ctx TypedPattern Sig where
  {-# INLINABLE evalSig #-}
  evalSig scope ctx env (AnnSig ann node) = case node of
    AppSig fun arg ->
      appValue (fmap (NbE.eval scope ctx env) ann) scope ctx (NbE.eval scope ctx env fun) (NbE.eval scope ctx env arg)
    FirstSig p  -> firstValue (fmap (NbE.eval scope ctx env) ann) (NbE.eval scope ctx env p)
    SecondSig p -> secondValue (fmap (NbE.eval scope ctx env) ann) (NbE.eval scope ctx env p)
    -- A singleton stays one under substitution, a type that is not one may
    -- become one: its value decides again.
    PiSig {} | not (isSingletonAnn ann) -> singletonFlag scope ctx (NbE.evalNode scope ctx env (AnnSig ann node))
    SigmaSig {} | not (isSingletonAnn ann) -> singletonFlag scope ctx (NbE.evalNode scope ctx env (AnnSig ann node))
    _ -> NbE.evalNode scope ctx env (AnnSig ann node)

  -- The observers of a λ apply the other value to the bound name, those of a
  -- pair project it. Each carries its type, so that it is refined as well.
  {-# INLINE etaMatchWith #-}
  etaMatchWith scoped term (AnnSig ann node) = case (ann, node) of
    (HasType ty, LamSig dom body) -> Just $ AnnSig
      (HasType (term ty (NbE.EtaTerm (\_ c -> typeOfValue c))))
      (LamSig (term dom (NbE.EtaTerm domainOf)) (scoped body (NbE.EtaScoped appliedTo)))
    (HasType ty, PairSig a b) -> Just $ AnnSig
      (HasType (term ty (NbE.EtaTerm (\_ c -> typeOfValue c))))
      (PairSig (term a (NbE.EtaTerm firstOf)) (term b (NbE.EtaTerm secondOf)))
    _ -> Nothing

  {-# INLINE extendScopedWith #-}
  extendScopedWith scoped term (AnnSig ann node) = AnnSig (fmap term ann) $ case node of
    LamSig dom body   -> LamSig (term dom) (scoped body (assumeBinder dom))
    PiSig dom body    -> PiSig (term dom) (scoped body (assumeBinder dom))
    SigmaSig dom body -> SigmaSig (term dom) (scoped body (assumeBinder dom))
    AppSig fun arg    -> AppSig (term fun) (term arg)
    FirstSig p        -> FirstSig (term p)
    SecondSig p       -> SecondSig (term p)
    PairSig a b       -> PairSig (term a) (term b)
    IdSig a x y       -> IdSig (term a) (term x) (term y)
    UniverseSig i     -> UniverseSig i
    UnitSig           -> UnitSig
    TTSig             -> TTSig
    ReflSig           -> ReflSig

  -- U i is a subtype of U j for i ≤ j, a Π is contravariant in its domain,
  -- and a Σ is covariant in both. The bound name of a Π or Σ has the smaller
  -- domain. Every other position is compared invariantly.
  {-# INLINE relateWith #-}
  relateWith scope ctx scoped term hd l@(AnnSig _ nodeL) r@(AnnSig _ nodeR) = case (nodeL, nodeR) of
    (UniverseSig i, UniverseSig j)
      | below (variance ctx) i j -> Just mempty
      | otherwise                -> Nothing
    (PiSig domL codL, PiSig domR codR) -> Just $
      term domL domR (withVariance (opposite (variance ctx)) ctx)
        <> scoped codL codR ctx (assumeBinder (smaller (opposite (variance ctx)) domL domR))
    (SigmaSig domL codL, SigmaSig domR codR) -> Just $
      term domL domR ctx <> scoped codL codR ctx (assumeBinder (smaller (variance ctx) domL domR))
    _ -> NbE.relateNodes scope (withVariance Invariant ctx) scoped term hd l r

  {-# INLINABLE refineVar #-}
  refineVar scope ctx x = refineAt scope ctx (NbE.vvar x) (typeOfName ctx x)

  -- A node in a value is a neutral only if it is an eliminator.
  {-# INLINABLE refineSig #-}
  refineSig scope ctx value (AnnSig ann node) = case node of
    AppSig {}    -> refineAt scope ctx value (typeOfNode ann node)
    FirstSig {}  -> refineAt scope ctx value (typeOfNode ann node)
    SecondSig {} -> refineAt scope ctx value (typeOfNode ann node)
    _            -> value

  -- A binder stands for its pattern's value, and bound to a value binds
  -- its leaves to the projections.
  {-# INLINE binderValue #-}
  binderValue scope ctx pat = Just (patternValue scope ctx pat)
  {-# INLINE bindValue #-}
  bindValue scope ctx env pat v = Just (bindPattern scope ctx env pat v)

  -- The types of a binder are moved under the environment.
  {-# INLINE evalBinder #-}
  evalBinder scope ctx env pat cont =
    enterPattern scope ctx env pat $ \extension pat' scope' _ _ -> cont (extendWith extension) pat' scope'

-- | Apply a function value to an argument value: a suspended lambda is
-- entered under its environment extended with the argument, any other
-- function is a stuck application of the type in the annotation.
appValue ::
  (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n) =>
  TypeAnn (TypeValue n) -> Scope n -> ctx n -> Value n -> Value n -> Value n
{-# INLINE appValue #-}
appValue ann scope ctx fun arg = NbE.eliminate fun $ \case
  NbE.VSuspended env (AnnSig _ (LamSig _ (ScopedAST pat body))) ->
    case assertDistinct pat of
      Distinct -> NbE.eval scope ctx (bindPattern scope ctx env pat arg) body
  NbE.Stuck fun' -> NbE.vnode (AnnSig ann (AppSig fun' arg))

-- | The first component of a pair value. Any other value gives a stuck
-- projection of the type in the annotation.
firstValue :: TypeAnn (TypeValue n) -> Value n -> Value n
{-# INLINE firstValue #-}
firstValue ann p = NbE.eliminate p $ \case
  NbE.VNode (AnnSig _ (PairSig a _)) -> a
  NbE.Stuck p' -> NbE.vnode (AnnSig ann (FirstSig p'))

-- | The second component of a pair value, like 'firstValue'.
secondValue :: TypeAnn (TypeValue n) -> Value n -> Value n
{-# INLINE secondValue #-}
secondValue ann p = NbE.eliminate p $ \case
  NbE.VNode (AnnSig _ (PairSig _ b)) -> b
  NbE.Stuck p' -> NbE.vnode (AnnSig ann (SecondSig p'))

-- | The projections for η of pairs and for the leaves of a pair pattern.
-- A stuck projection carries its type, read off the Σ type of the value
-- when the projection is refined; a projection of a pair does not read it.
firstOf :: HasTypes ctx => Scope n -> ctx n -> Value n -> Value n
{-# INLINE firstOf #-}
firstOf _ ctx p = firstValue (HasType (domainOfSigma (typeOfValue ctx p))) p

secondOf :: (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> Value n -> Value n
{-# INLINE secondOf #-}
secondOf scope ctx p = secondValue (HasType (codomainOfSigma scope ctx (typeOfValue ctx p) (firstOf scope ctx p))) p

-- | The domain of a Σ type, and its codomain at a value.
domainOfSigma :: TypeValue n -> TypeValue n
domainOfSigma ty = case NbE.force ty of
  NbE.VSuspended _ (AnnSig _ (SigmaSig a _)) -> a
  _ -> impossibleNonSigmaType

codomainOfSigma :: (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> TypeValue n -> Value n -> TypeValue n
codomainOfSigma scope ctx ty a = case NbE.force ty of
  NbE.VSuspended env (AnnSig _ (SigmaSig _ cod)) -> codomainAt scope ctx env cod a
  _ -> impossibleNonSigmaType

-- | Impossible: conversion compares two values of one type, so the value
-- that η compares with a pair has the pair's type, which is a Σ, and so
-- does the value a pair pattern is bound to.
impossibleNonSigmaType :: a
impossibleNonSigmaType = error "DependentTypes: impossible: a projection of a value whose type is not a Σ"

-- | The observers of η for a λ: the domain of the other value's type, and the
-- other value applied to the bound name.
domainOf :: HasTypes ctx => Scope n -> ctx n -> Value n -> TypeValue n
{-# INLINE domainOf #-}
domainOf _ ctx f = case NbE.force (typeOfValue ctx f) of
  NbE.VSuspended _ (AnnSig _ (PiSig dom _)) -> dom
  _ -> impossibleNonPiType

appliedTo ::
  (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n, DExt n l) =>
  Scope l -> ctx l -> TypedPattern n l -> Value l -> Value l
{-# INLINE appliedTo #-}
appliedTo scope ctx pat f = case NbE.force (typeOfValue ctx f) of
  NbE.VSuspended env (AnnSig _ (PiSig _ cod)) ->
    let arg = patternValue scope ctx pat
    in appValue (HasType (codomainAt scope ctx env cod arg)) scope ctx f arg
  _ -> impossibleNonPiType

-- | Impossible: conversion compares two values of one type, so the value
-- that η compares with a λ has the λ's type, which is a Π.
impossibleNonPiType :: a
impossibleNonPiType = error "DependentTypes: impossible: η for a λ against a value whose type is not a Π"

-- | The type of a value, read off its head: the type of a name from the
-- context, the type of a node from its annotation. The head is the folded
-- one, so that a defined name keeps the type its declaration gives it,
-- and not the type its body computes (see 'NbE.forceFolded').
typeOfValue :: HasTypes ctx => ctx n -> Value n -> TypeValue n
{-# INLINE typeOfValue #-}
typeOfValue ctx v = case NbE.forceFolded v of
  NbE.VVar x -> typeOfName ctx x
  NbE.VNode (AnnSig ann node) -> typeOfNode ann node
  NbE.VSuspended _ (AnnSig ann node) -> typeOfNode ann node

-- | Whether two universe levels are related in a direction.
below :: Variance -> Integer -> Integer -> Bool
{-# INLINE below #-}
below = \case
  Covariant     -> (<=)
  Contravariant -> (>=)
  Invariant     -> (==)

-- | The smaller of two types compared in a direction.
smaller :: Variance -> a -> a -> a
{-# INLINE smaller #-}
smaller = \case
  Contravariant -> \_ r -> r
  _             -> \l _ -> l

-- | The context under the binder of a scoped position whose domain is the
-- given type: a variable is assumed at the domain, which is a value
-- already, and the names of a pair pattern at their own types.
assumeBinder :: HasTypes ctx => TypeValue n -> Extend ctx TypedPattern Sig n
{-# INLINE assumeBinder #-}
assumeBinder ty = Extend $ \scope pat _ ctx -> case pat of
  TypedVar x _ -> assume x ty ctx
  TypedPair {} -> assumePattern scope ctx pat

-- | The context under a binder, each name assumed at its type.
assumePattern :: (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> TypedPattern n l -> ctx l
assumePattern scope ctx pat = case pat of
  TypedVar x ty -> case (assertDistinct x, assertExt x) of
    (Distinct, Ext) -> assume x (NbE.eval scope ctx identitySubst ty) ctx
  TypedPair _ l r -> case assertDistinct l of
    Distinct -> assumePattern (extendScopePattern l scope) (assumePattern scope ctx l) r

-- | Enter a binder under an environment ('NbE.evalBinder'): refresh each
-- name for the scope, and evaluate each type under the environment so far
-- and read it back, in the context with the names before it assumed. The
-- continuation also receives that context and environment.
enterPattern ::
  (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n, Distinct i) =>
  Scope n -> ctx n -> Substitution Value i n -> TypedPattern i l ->
  (forall n'. DExt n n' => Extension i l n n' -> TypedPattern n n' -> Scope n' -> ctx n' -> Substitution Value l n' -> r) ->
  r
enterPattern scope ctx env pat cont = case pat of
  TypedVar x ty ->
    let tyV = NbE.eval scope ctx env ty
    in withRefreshed scope (nameOf x) $ \x' ->
         let extension = Extension (\subst -> addRename (sink subst) x (nameOf x'))
         in cont extension (TypedVar x' (NbE.quote scope ctx tyV)) (extendScope x' scope)
              (assume x' tyV ctx) (extendWith extension env)
  TypedPair ty l r -> case assertDistinct l of
    Distinct ->
      enterPattern scope ctx env l $ \extensionL l' scopeL ctxL envL ->
        enterPattern scopeL ctxL envL r $ \extensionR r' scopeR ctxR envR ->
          let pat' = TypedPair (NbE.quote scope ctx (NbE.eval scope ctx env ty)) l' r'
          in case assertExt pat' of
               Ext -> cont (extensionL `andThen` extensionR) pat' scopeR ctxR envR

-- | The extension of a substitution by the names of a binder, for any kind
-- of substituted terms.
newtype Extension i l n n' = Extension
  (forall e. (Sinkable e, InjectName e) => Substitution e i n -> Substitution e l n')

extendWith :: (Sinkable e, InjectName e) => Extension i l n n' -> Substitution e i n -> Substitution e l n'
extendWith (Extension extend) = extend

andThen :: Extension i j n m -> Extension j l m n' -> Extension i l n n'
andThen (Extension f) (Extension g) = Extension (g . f)

-- | The value a binder stands for: a variable stands for its name, a pair
-- pattern for the pair of what its components stand for, with its Σ type.
patternValue :: forall ctx n l. (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct l) => Scope l -> ctx l -> TypedPattern n l -> Value l
patternValue scope ctx = go
  where
    go :: forall a b. Ext b l => TypedPattern a b -> Value l
    go pat = case pat of
      TypedVar x _     -> NbE.vvar (sink (nameOf x))
      TypedPair ty l r -> NbE.vnode (AnnSig (HasType (sunkType pat ty)) (PairSig (goLeft r l) (go r)))

    -- One scope extension is composed at a time: GHC solves an 'Ext' through
    -- one chain of givens only.
    sunkType :: forall a b. Ext b l => TypedPattern a b -> Elaborated a -> TypeValue l
    sunkType pat ty = case assertExt pat of
      Ext -> NbE.eval scope ctx identitySubst (sink ty)

    goLeft :: forall a i b. Ext b l => TypedPattern i b -> TypedPattern a i -> Value l
    goLeft r l = case assertExt r of
      Ext -> go l

-- | An environment extended with a binder bound to a value: a variable is
-- bound to the value, the components of a pair pattern to its projections,
-- which are computed when a name is looked up.
bindPattern ::
  (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct o) =>
  Scope o -> ctx o -> Substitution Value i o -> TypedPattern i l -> Value o -> Substitution Value l o
bindPattern scope ctx env pat v = case pat of
  TypedVar x _    -> addSubst env x v
  TypedPair _ l r -> bindPattern scope ctx (bindPattern scope ctx env l (firstOf scope ctx v)) r (secondOf scope ctx v)

-- | The codomain of a Π or Σ type at a value, from the environment and the
-- codomain of the type's value.
codomainAt ::
  (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n, Distinct i) =>
  Scope n -> ctx n -> Substitution Value i n -> ScopedAST TypedPattern Sig i -> Value n -> TypeValue n
{-# INLINE codomainAt #-}
codomainAt scope ctx env (ScopedAST pat cod) arg = case assertDistinct pat of
  Distinct -> NbE.eval scope ctx (bindPattern scope ctx env pat arg) cod

-- | A Π or Σ type value, annotated with whether it is a singleton. The flag
-- is lazy and decided one level down, from the flags of the parts' values: a
-- Π is a singleton if its codomain at a fresh name is, a Σ if its domain and
-- codomain are.
singletonFlag :: (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> TypeValue n -> TypeValue n
{-# INLINE singletonFlag #-}
singletonFlag scope ctx value = case NbE.force value of
  NbE.VSuspended env (AnnSig ann node@(PiSig dom cod)) ->
    NbE.vsuspended env (AnnSig (typeAnnotation (typeOfNode ann node) (singletonCodomain scope ctx dom env cod)) node)
  NbE.VSuspended env (AnnSig ann node@(SigmaSig dom cod)) ->
    NbE.vsuspended env (AnnSig (typeAnnotation (typeOfNode ann node) (isSingletonType dom && singletonCodomain scope ctx dom env cod)) node)
  _ -> value

-- | Whether the codomain of a Π or Σ type is a singleton at a fresh name.
singletonCodomain ::
  (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n, Distinct i) =>
  Scope n -> ctx n -> TypeValue n -> Substitution Value i n -> ScopedAST TypedPattern Sig i -> Bool
{-# INLINE singletonCodomain #-}
singletonCodomain scope ctx dom env cod = withFresh scope $ \x ->
  isSingletonType (codomainAt (extendScope x scope) (assume x dom ctx) (sink env) cod (NbE.vvar (nameOf x)))

-- | A neutral of a singleton type is that type's one value. Any other stays.
refineAt :: (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> Value n -> TypeValue n -> Value n
{-# INLINE refineAt #-}
refineAt scope ctx value ty
  | isSingletonType ty = canonicalSingleton scope ctx ty
  | otherwise          = value

-- | The one value of a singleton type: @tt@, a λ whose body is the one value
-- of the codomain, or the pair of the one values.
canonicalSingleton :: (Eval ctx TypedPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> TypeValue n -> Value n
{-# INLINABLE canonicalSingleton #-}
{-# SPECIALIZE canonicalSingleton :: Distinct n => Scope n -> Typing n -> TypeValue n -> Value n #-}
canonicalSingleton scope ctx ty = case NbE.force ty of
  NbE.VNode (AnnSig _ UnitSig) -> NbE.vnode (AnnSig (HasType unitType) TTSig)
  NbE.VSuspended env (AnnSig _ (PiSig dom cod)) -> withFresh scope $ \x ->
    let scope' = extendScope x scope
        ctx' = assume x dom ctx
        body = NbE.quote scope' ctx' (canonicalSingleton scope' ctx' (codomainAt scope' ctx' (sink env) cod (NbE.vvar (nameOf x))))
    in NbE.vsuspended identitySubst (AnnSig (HasType ty) (LamSig dom (ScopedAST (TypedVar x (NbE.quote scope ctx dom)) body)))
  NbE.VSuspended env (AnnSig _ (SigmaSig dom cod)) ->
    let a = canonicalSingleton scope ctx dom
    in NbE.vnode (AnnSig (HasType ty) (PairSig a (canonicalSingleton scope ctx (codomainAt scope ctx env cod a))))
  _ -> error "DependentTypes: impossible: the one value of a type that is not a singleton"

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

-- | Whether the first type is a subtype of the second.
isSubtype :: Distinct n => Scope n -> Typing n -> TypeValue n -> TypeValue n -> Bool
{-# INLINE isSubtype #-}
isSubtype scope typing = Conv.conv scope (withVariance Covariant typing)
