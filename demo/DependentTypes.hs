{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}
-- The Show instance of a synonym over library types.
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Dependent functions and pairs over a universe, with a unit type: a
-- language whose context holds types. Its terms are elaborated (see
-- "DependentTypes.Elaborate"): every binder carries its type, and an
-- eliminator, an application or a projection, carries the type of its
-- result as free-foil's annotation. Every other node is annotated 'Nothing'.
-- Under a binder the language gives the bound name its type, the domain of
-- the @λ@, @Π@ or @Σ@ ('NbE.extendScopedWith').
--
-- The language uses both sides of η. The types decide η for functions and
-- the unit type ('NbE.refineVar', 'NbE.refineSig'): a neutral of type
-- @Unit@ is @tt@, and a neutral @f@ of type @(x : A) -> B@ is
-- @\\(x : A). f x@. A variable finds its type in the context, an eliminator
-- in its annotation. So in a context of types ('Typing') @\\(x : Unit). x@
-- normalises to @\\(x : Unit). tt@, while with 'NbE.NoContext' variables
-- have no types. Pairs have η by shape ('NbE.etaMatchWith'): conversion
-- compares a pair with another value through the projections, so @p@ and
-- @(first p, second p)@ are convertible, and @p@ is a normal form.
--
-- The grammar follows the monolithic language's, with the projections
-- named as in Rzk, and the modules follow Renata Shakirova's pairs language.
module DependentTypes
  ( -- * Terms
    Sig
  , Elaborated
  , Raw
  , Value
  , unannotated
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
import Data.Bifunctor (bimap)
import FreeFoil.NbE (Eval (..), Extend (..), HasDefinitions (..), HasHeads (..), NoContext (..))
import qualified FreeFoil.NbE as NbE
import qualified FreeFoil.NbE.Conversion as Conv

import DependentTypes.Generated (FFPattern (..), FFTerm, TermSig (..))

-- | The signature of elaborated terms.
type Sig = AnnSig Maybe TermSig

-- | Elaborated terms in scope @n@.
type Elaborated n = AST FFPattern Sig n

-- | Terms as parsed, before elaboration.
type Raw n = FFTerm n

-- | Semantic values.
type Value = NbE.Value FFPattern Sig

-- | A term without its annotations.
unannotated :: Elaborated n -> Raw n
unannotated = hoistAST (\(AnnSig _ node) -> node)

-- | Terms print without their annotations.
instance Show (AST FFPattern Sig n) where
  show = show . unannotated

-- | The universe, whose type is itself.
universe :: Value n
universe = NbE.VNode (AnnSig Nothing UniverseSig)

-- | The unit type.
unitType :: Value n
unitType = NbE.VNode (AnnSig Nothing UnitSig)

-- * Contexts of types

-- | What the language needs of a context: the types of names.
class HasTypes ctx where
  -- | The context under a binder of one name of a type.
  assume :: DExt n l => NameBinder n l -> Value n -> ctx n -> ctx l
  -- | The type of a name, if the context knows it.
  typeOfName :: ctx n -> Name n -> Maybe (Value n)

-- | No types, so normalisation is untyped, except for the types in the
-- annotations.
instance HasTypes NoContext where
  assume _ _ _ = NoContext
  typeOfName _ _ = Nothing

-- | A type for every name in scope.
newtype Typing n = Typing (NameMap n (Value n))

-- | The context of the empty scope.
emptyTyping :: Typing VoidS
emptyTyping = Typing emptyNameMap

-- | The type of a name.
typeOf :: Name n -> Typing n -> Value n
typeOf x (Typing types) = lookupName x types

instance HasTypes Typing where
  assume x ty (Typing types) = Typing (addNameBinder x (sink ty) (sink1 types))
  typeOfName (Typing types) x = Just (lookupName x types)

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

-- | β for functions and for projections of a pair, the types of bound
-- names, η at the types of functions and of the unit type, and η of pairs
-- by shape.
instance (HasTypes ctx, HasDefinitions ctx FFPattern Sig) => Eval ctx FFPattern Sig where
  {-# INLINABLE evalSig #-}
  evalSig scope ctx env (AnnSig ann node) = case node of
    AppSig fun arg ->
      appValue (fmap (NbE.eval scope ctx env) ann) scope ctx (NbE.eval scope ctx env fun) (NbE.eval scope ctx env arg)
    FirstSig p  -> firstValue (fmap (NbE.eval scope ctx env) ann) (NbE.eval scope ctx env p)
    SecondSig p -> secondValue (fmap (NbE.eval scope ctx env) ann) (NbE.eval scope ctx env p)
    _ -> NbE.evalNode scope ctx env (AnnSig ann node)

  {-# INLINE etaMatchWith #-}
  etaMatchWith _ term (AnnSig _ node) = case node of
    PairSig a b -> Just (AnnSig Nothing (PairSig (term a (NbE.EtaTerm firstOf)) (term b (NbE.EtaTerm secondOf))))
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
  refineVar scope ctx x = case typeOfName ctx x of
    Just ty -> expandAt scope ctx (NbE.VVar x) ty
    Nothing -> NbE.VVar x

  -- Only an eliminator has an annotation.
  {-# INLINABLE refineSig #-}
  refineSig scope ctx value (AnnSig ann _) = case ann of
    Just ty -> expandAt scope ctx value ty
    Nothing -> value

-- | Apply a function value to an argument value: a suspended lambda is
-- entered under its environment extended with the argument, any other
-- function is a stuck application of the type in the annotation.
appValue ::
  (Eval ctx FFPattern Sig, Distinct n) =>
  Maybe (Value n) -> Scope n -> ctx n -> Value n -> Value n -> Value n
{-# INLINE appValue #-}
appValue ann scope ctx fun arg = case fun of
  NbE.VSuspended env (AnnSig _ (LamSig _ (ScopedAST (FFPatternVar x) body))) ->
    case assertDistinct x of
      Distinct -> NbE.eval scope ctx (addSubst env x arg) body
  _ -> NbE.VNode (AnnSig ann (AppSig fun arg))

-- | The first component of a pair value. Any other value gives a stuck
-- projection of the type in the annotation.
firstValue :: Maybe (Value n) -> Value n -> Value n
firstValue ann p = case p of
  NbE.VNode (AnnSig _ (PairSig a _)) -> a
  _ -> NbE.VNode (AnnSig ann (FirstSig p))

-- | The second component of a pair value, like 'firstValue'.
secondValue :: Maybe (Value n) -> Value n -> Value n
secondValue ann p = case p of
  NbE.VNode (AnnSig _ (PairSig _ b)) -> b
  _ -> NbE.VNode (AnnSig ann (SecondSig p))

-- | The projections that compare a pair with another value by η. A
-- projection of a neutral whose type is known is annotated with its type,
-- so that it is refined as well.
firstOf :: (HasTypes ctx, Distinct n) => Scope n -> ctx n -> Value n -> Value n
firstOf _ ctx p = firstValue (typeOfNeutral ctx p >>= sigmaDomain) p

secondOf :: (Eval ctx FFPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> Value n -> Value n
secondOf scope ctx p = secondValue (fmap (\ty -> codomainAt scope ctx ty (firstOf scope ctx p)) (typeOfNeutral ctx p)) p

-- | The type of a neutral: of a variable from the context, of an eliminator
-- from its annotation.
typeOfNeutral :: HasTypes ctx => ctx n -> Value n -> Maybe (Value n)
typeOfNeutral ctx = \case
  NbE.VVar x -> typeOfName ctx x
  NbE.VNode (AnnSig ty _) -> ty
  NbE.VSuspended _ (AnnSig ty _) -> ty

-- | The domain of a Σ type.
sigmaDomain :: Value n -> Maybe (Value n)
sigmaDomain = \case
  NbE.VSuspended _ (AnnSig _ (SigmaSig a _)) -> Just a
  _ -> Nothing

-- | The binder of one name of a type.
assumeVar :: HasTypes ctx => Value n -> Extend ctx FFPattern Sig n
assumeVar ty = Extend $ \_ pat _ ctx -> case pat of
  FFPatternVar x -> assume x ty ctx

-- | The codomain of a Π or Σ type at a value.
codomainAt :: forall ctx n. (Eval ctx FFPattern Sig, Distinct n) => Scope n -> ctx n -> Value n -> Value n -> Value n
codomainAt scope ctx ty arg = case ty of
  NbE.VSuspended env (AnnSig _ (PiSig _ (ScopedAST (FFPatternVar b) cod))) -> at env b cod
  NbE.VSuspended env (AnnSig _ (SigmaSig _ (ScopedAST (FFPatternVar b) cod))) -> at env b cod
  _ -> error "DependentTypes: not a Π or Σ type"
  where
    at :: forall i l. Distinct i => Substitution Value i n -> NameBinder i l -> Elaborated l -> Value n
    at env b cod = case assertDistinct b of
      Distinct -> NbE.eval scope ctx (addSubst env b arg) cod

-- | η-expand a neutral at its type.
expandAt :: (Eval ctx FFPattern Sig, HasTypes ctx, Distinct n) => Scope n -> ctx n -> Value n -> Value n -> Value n
expandAt scope ctx value ty = case ty of
  NbE.VNode (AnnSig _ UnitSig) -> NbE.VNode (AnnSig Nothing TTSig)
  NbE.VSuspended _ (AnnSig _ (PiSig dom _)) -> expandFunction scope ctx value ty dom
  _ -> value

-- | A neutral @f : (x : A) -> B@ as the value of @\\(x : A). f x@, whose
-- application is annotated with @B@. The value of @f@ sits in the
-- environment under a fresh name @g@.
expandFunction ::
  (Eval ctx FFPattern Sig, HasTypes ctx, Distinct n) =>
  Scope n -> ctx n -> Value n -> Value n -> Value n -> Value n
expandFunction scope ctx fun ty dom =
  withFresh scope $ \g ->
    let scopeG = extendScope g scope
        ctxG = assume g ty ctx
    in withFresh scopeG $ \x ->
         let scopeX = extendScope x scopeG
             ctxX = assume x (sink dom) ctxG
             cod = NbE.quote scopeX ctxX (codomainAt scopeX ctxX (sinkPast x (sinkPast g ty)) (NbE.VVar (nameOf x)))
             body = Node (AnnSig (Just cod) (AppSig (Var (sink (nameOf g))) (Var (nameOf x))))
         in NbE.VSuspended (addSubst identitySubst g fun)
              (AnnSig Nothing (LamSig dom (ScopedAST (FFPatternVar x) body)))

-- | A value under a binder.
sinkPast :: DExt n l => NameBinder n l -> Value n -> Value l
sinkPast _ = sink

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
