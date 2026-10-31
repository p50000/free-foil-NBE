{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
-- | Normalisation by evaluation, generic in the signature of the object
-- language. A language is a signature bifunctor @sig@ and a binder type, as
-- in "Control.Monad.Free.Foil"; to normalise its terms it supplies one 'Eval'
-- instance, its elimination rules. The semantic domain ('Value'), evaluation
-- ('eval'), readback ('quote') and the normalisers 'nf' and 'whnf' are
-- generic.
--
-- The normaliser is untyped and intensional: it decides β and the language's
-- own reductions, not η, and it keeps one signature for terms and values, so
-- neutral and normal values are not told apart by type (see 'Value').
-- Conversion checking adds η for the introduction forms a language describes
-- with 'etaMatchWith'.
--
-- A language's signature must be a 'Bifunctor' and a 'Bifoldable', both
-- derivable, and representational in both parameters (see 'evalNode'). Its
-- binder type must be 'Foil.CoSinkable', which free-foil generates, plus
-- 'Foil.SinkableK' for 'whnf', which has a generic default.
--
-- Evaluation, readback and conversion carry a context the client supplies
-- ('Context'); 'Foil.Scope' is the instance the library uses, and a language
-- states in its 'Eval' instance what it needs of the context.
--
-- A language specialises 'nf', 'eval' and 'quote' to its types, next to
-- its 'Eval' instance, keeping the scope polymorphic and fixing the context
-- to 'Foil.Scope':
--
-- > type Term n = AST Pattern TermSig n
-- > type Value n = NbE.Value Pattern TermSig n
-- >
-- > {-# SPECIALIZE NbE.nf    :: Distinct n => Scope n -> Term n -> Term n #-}
-- > {-# SPECIALIZE NbE.eval  :: (Distinct o, Distinct i) =>
-- >       Scope o -> Substitution Value i o -> Term i -> Value o #-}
-- > {-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> Value n -> Term n #-}
--
-- and likewise 'FreeFoil.NbE.Conversion.conv' and
-- 'FreeFoil.NbE.Conversion.convertible', and a helper of its own that takes
-- the context, such as an application of values shared by β and the η
-- observer. Without the pragmas the monolithic
-- demonstration language is 1.25× to 1.4× slower: GHC's own specialisation
-- at a call site fixes the scope too, so it ends at the first binder, and it
-- never specialises the calls to 'eval' inside the instance.
module FreeFoil.NbE
  ( -- * Semantic domain
    Value (..)
    -- * Context
  , Context (..)
    -- * Evaluation
  , Eval (..)
  , eval
  , evalNode
    -- * η
  , EtaTerm (..)
  , EtaScoped (..)
    -- * Readback
  , quote
  , quoteScoped
  , nf
  , quoteWhnf
  , freezeScoped
  , whnf
  ) where

import qualified Control.Monad.Foil          as Foil
import qualified Control.Monad.Foil.Internal as Foil (Substitution (..))
import           Control.Monad.Free.Foil     (AST (..), ScopedAST (..), substitute)
import           Data.Bifoldable             (Bifoldable (..))
import           Data.Bifunctor              (Bifunctor (..))
import qualified Data.IntMap                 as IntMap
import           Data.Monoid                 (Any (..))
import           Data.Void                   (Void, absurd)
import           Unsafe.Coerce               (unsafeCoerce)

-- * Semantic domain

-- | A semantic value in scope @n@. Term subterms are values already; only
-- scoped subterms, the bodies under binders, are suspended. A 'VSuspended'
-- node keeps its term subterms as values, its scoped subterms as syntax, and
-- one captured environment for them all: a @Pi@ holds its domain as a value
-- while its codomain waits, unevaluated, for the environment. Since 'eval'
-- and 'quote' each visit every subterm exactly once, readback is linear in
-- the size of the term, and nested @Pi@ types do not re-normalise their
-- codomains.
--
-- /Invariant./ Every value 'eval' produces is weak-head normal at every
-- position: no node is an eliminator applied to the introduction form it
-- eliminates. The type cannot enforce this, as it does not know which
-- constructors of @sig@ eliminate; the language's 'evalSig' establishes it,
-- and every function here preserves it.
data Value binder sig n where
  -- | A neutral variable.
  VVar :: {-# UNPACK #-} !(Foil.Name n) -> Value binder sig n
  -- | A node without scoped subterms.
  VNode :: sig Void (Value binder sig n) -> Value binder sig n
  -- | A node with scoped subterms, suspended under its environment; the
  -- environment sits in the constructor, so the node costs one heap object
  -- beside its @sig@ cell.
  VSuspended ::
    Foil.Distinct i =>
    Foil.Substitution (Value binder sig) i n ->
    sig (ScopedAST binder sig i) (Value binder sig n) ->
    Value binder sig n

instance Foil.InjectName (Value binder sig) where
  injectName = VVar

instance Bifunctor sig => Foil.Sinkable (Value binder sig) where
  sinkabilityProof :: (Foil.Name n -> Foil.Name l) -> Value binder sig n -> Value binder sig l
  sinkabilityProof rename (VVar x) =
    VVar (rename x)
  sinkabilityProof rename (VNode node) =
    VNode (bimap id (Foil.sinkabilityProof rename) node)
  sinkabilityProof rename (VSuspended env node) =
    VSuspended (Foil.sinkabilityProof rename env) (bimap id (Foil.sinkabilityProof rename) node)

-- * Context

-- | The context that evaluation, readback and conversion carry, indexed by
-- the scope. Under a binder the core extends it with 'extendContext',
-- passing the scope under the binder, and relies on 'contextScope' of the
-- result being that scope. 'Foil.Scope' is the simplest instance.
class Context ctx where
  -- | The scope of the context.
  contextScope :: ctx n -> Foil.Scope n
  -- | The context under a binder: given the binder, refreshed for the
  -- context's scope, and the scope under it, which free-foil computes when
  -- it refreshes the binder.
  extendContext ::
    (Foil.CoSinkable binder, Foil.Distinct n, Foil.DExt n l) =>
    binder n l -> Foil.Scope l -> ctx n -> ctx l

instance Context Foil.Scope where
  {-# INLINE contextScope #-}
  contextScope = id
  {-# INLINE extendContext #-}
  extendContext _ scope _ = scope

-- * η

-- | The observer of a term position of an introduction form: the eliminator
-- of that position, from the context and any value to the component. The two
-- observers of a pair are @fst@ and @snd@.
newtype EtaTerm ctx binder sig n =
  EtaTerm (ctx n -> Value binder sig n -> Value binder sig n)

-- | The observer of a scoped position of an introduction form: from the
-- context under the position's refreshed binder, that binder, and the other
-- value sunk into that scope, the eliminator applied to the names the binder
-- binds. The observer of a lambda's body applies the other value to the
-- bound name. The outer scope is distinct so that an observer may list the
-- binder's names.
newtype EtaScoped ctx binder sig n =
  EtaScoped
    (forall l. (Foil.Distinct n, Foil.DExt n l) =>
      ctx l -> binder n l -> Value binder sig l -> Value binder sig l)

-- * Evaluation

-- | A language becomes an NbE instance by giving its elimination rules:
-- 'evalSig' receives a raw node and the environment, matches the
-- eliminators, evaluates the principal subterm and either reduces or, on a
-- neutral, rebuilds the node as a 'VNode'. Every other node falls through to
-- 'evalNode'. The node arrives raw so that a redex never builds the
-- interpreted node it would discard. The instance upholds the 'Value'
-- invariant; "LambdaPi" is a one-rule example. An instance comes with the
-- @SPECIALIZE@ pragmas shown in the module header.
class (Context ctx, Bifunctor sig, Bifoldable sig) => Eval ctx binder sig where
  evalSig ::
    (Foil.Distinct o, Foil.Distinct i) =>
    ctx o ->
    Foil.Substitution (Value binder sig) i o ->
    sig (ScopedAST binder sig i) (AST binder sig i) ->
    Value binder sig o
  evalSig = evalNode

  -- | The η law of an introduction form, for conversion checking, in the
  -- style of 'Data.ZipMatchK.zipMatchWith2':
  --
  -- > etaMatchWith _ term = \case
  -- >   PairSig a b -> Just (PairSig (term a (EtaTerm (const fstValue))) (term b (EtaTerm (const sndValue))))
  -- >   _ -> Nothing
  --
  -- A constructor with an η law combines each of its positions with the
  -- position's observer, a t'EtaScoped' or a t'EtaTerm'. Any other
  -- constructor answers 'Nothing', the default. Whether the answer is a
  -- 'Just' depends only on the node, not on its subterms. A lambda observes
  -- its body by applying the other value to the bound name (Coquand 1996),
  -- a pair observes its components by the projections (Abel and Coquand
  -- 2007).
  etaMatchWith ::
    (a -> EtaScoped ctx binder sig n -> c) ->
    (b -> EtaTerm ctx binder sig n -> d) ->
    sig a b ->
    Maybe (sig c d)
  {-# INLINE etaMatchWith #-}
  etaMatchWith _ _ _ = Nothing

-- | Evaluate a term under an environment: look variables up, hand nodes to
-- 'evalSig'. A variable that the environment does not map is a neutral.
eval ::
  (Eval ctx binder sig, Foil.Distinct o, Foil.Distinct i) =>
  ctx o ->
  Foil.Substitution (Value binder sig) i o ->
  AST binder sig i ->
  Value binder sig o
{-# INLINABLE eval #-}
eval ctx !env = \case
  Var x -> Foil.lookupSubst env x
  Node node -> evalSig ctx env node

-- | Evaluate a node that has no elimination rule: suspend it whole under the
-- environment if it has scoped subterms, otherwise evaluate its term
-- subterms. The same environment both suspends the node and drives its
-- subterms. A node with no subterms of one kind is reused by coercion, which
-- requires the signature to be representational in both parameters; every
-- ordinary data type is.
evalNode ::
  (Eval ctx binder sig, Foil.Distinct o, Foil.Distinct i) =>
  ctx o ->
  Foil.Substitution (Value binder sig) i o ->
  sig (ScopedAST binder sig i) (AST binder sig i) ->
  Value binder sig o
{-# INLINE evalNode #-}
evalNode ctx env node =
  case ensureBivacuousFirst node of
    Just node' -> VNode (bimap absurd (eval ctx env) node')
    Nothing -> VSuspended env $ case ensureBivacuousSecond node of
      -- Nothing to evaluate either (a lambda, say): reuse the cell as it is.
      Just node' -> vacuous node'
      Nothing    -> bimap id (eval ctx env) node

-- A node whose parameter positions are provably empty is the same heap
-- object at any parameter type, so it is reused by coercion rather than
-- rebuilt field by field. The coercions are sound because a signature
-- bifunctor is representational in its parameters; the emptiness tests
-- constant-fold per constructor in specialised code.

vacuous :: f Void -> f a
vacuous = unsafeCoerce

ensureBivacuousFirst :: Bifoldable f => f a b -> Maybe (f Void b)
{-# INLINE ensureBivacuousFirst #-}
ensureBivacuousFirst x
  | getAny (bifoldMap (const (Any True)) (const (Any False)) x) = Nothing
  | otherwise = Just (unsafeCoerce x)

ensureBivacuousSecond :: Bifoldable f => f a b -> Maybe (f a Void)
{-# INLINE ensureBivacuousSecond #-}
ensureBivacuousSecond x
  | getAny (bifoldMap (const (Any False)) (const (Any True)) x) = Nothing
  | otherwise = Just (unsafeCoerce x)

-- * Readback

-- | Read a value back into a term. Term subterms recurse directly; scoped
-- subterms are read back under their binder by 'quoteScoped'.
--
-- Every constraint here is used. An unused dictionary would make GHC split
-- 'quote' into a wrapper and a worker, and a @SPECIALIZE@ pragma would then
-- specialise only the wrapper.
quote ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  ctx n ->
  Value binder sig n ->
  AST binder sig n
{-# INLINABLE quote #-}
quote ctx = \case
  VVar x -> Var x
  VNode node -> Node $! bimap absurd (quote ctx) node
  VSuspended env node -> Node $! bimap (quoteScoped ctx env) (quote ctx) node

-- | Read back one scoped subterm of a suspended node: refresh the binder,
-- extend the context and the captured environment with it, the latter as a
-- fresh neutral, evaluate the body once under them, and quote the result. It
-- inlines into 'quote', so it is specialised with it.
quoteScoped ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder) =>
  ctx n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
{-# INLINE quoteScoped #-}
quoteScoped ctx env (ScopedAST binder body) =
  Foil.withRefreshedPattern (contextScope ctx) binder $ \extendEnv binder' scope' ->
    case Foil.assertDistinct binder of
      Foil.Distinct ->
        let ctx' = extendContext binder' scope' ctx
        in ScopedAST binder' (quote ctx' (eval ctx' (extendEnv env) body))

-- | Normal form: evaluate, then read back fully.
--
-- > nf (λf. (λg. λx. g x) f)  =  λf. λx. f x
--
-- The normal form is β-normal but not η-short. For example, @nf@ does not
-- contract @λx. f x@ to @f@, although 'FreeFoil.NbE.Conversion.conv'
-- identifies the two. Contraction can change the type of a term. In Rocq
-- the type of @f@ need not be convertible to the type of @λx. f x@, which is
-- why Rocq defines η-expansion but no η-reduction
-- (<https://rocq-prover.org/doc/master/refman/language/core/conversion.html#expansion Rocq reference manual, η-expansion>).
-- In Rzk an η-expanded witness of an extension type type-checks where the
-- contracted one does not (Kudasov, Sim and Ahrens,
-- /Rzk: a Proof Assistant for Synthetic ∞-Categories/, 2026, Remark 4.5,
-- <https://arxiv.org/abs/2607.12207>). So readback keeps the η-shape of the
-- term.
nf ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  ctx n ->
  AST binder sig n ->
  AST binder sig n
{-# INLINABLE nf #-}
nf ctx = quote ctx . eval ctx Foil.identitySubst

-- | Read back the head of a value only: quote its term subterms, which are
-- values already, and freeze its scoped subterms instead of normalising under
-- their binders.
quoteWhnf ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  ctx n ->
  Value binder sig n ->
  AST binder sig n
quoteWhnf ctx = \case
  VVar x -> Var x
  VNode node -> Node $ bimap absurd (quote ctx) node
  VSuspended env node -> Node $ bimap (freezeScoped ctx env) (quote ctx) node

-- | Freeze one scoped subterm of a suspended node without evaluating under
-- its binder: refresh the binder and substitute the captured environment,
-- quoted to terms, into the still-syntactic body. 'substitute' only renames,
-- so a redex under the binder survives.
freezeScoped ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  ctx n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
freezeScoped ctx env (ScopedAST binder body) =
  Foil.withRefreshedPattern (contextScope ctx) binder $ \extendSubst binder' scope' ->
    ScopedAST binder' (substitute scope' (extendSubst (quoteSubst ctx env)) body)

-- | Quote every value in an environment, turning it into a syntactic
-- substitution.
quoteSubst ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  ctx n ->
  Foil.Substitution (Value binder sig) i n ->
  Foil.Substitution (AST binder sig) i n
quoteSubst ctx (Foil.UnsafeSubstitution m) =
  Foil.UnsafeSubstitution (IntMap.map (quote ctx) m)

-- | Weak-head normal form: evaluate, then read back the head only. Shares
-- 'eval' with 'nf'; 'quoteWhnf' does not go under binders, so a redex
-- under a lambda survives. Term positions are values already, so the two
-- readbacks differ only at scoped positions.
whnf ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  ctx n ->
  AST binder sig n ->
  AST binder sig n
whnf ctx = quoteWhnf ctx . eval ctx Foil.identitySubst
