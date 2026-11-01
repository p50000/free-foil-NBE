{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE KindSignatures        #-}
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
-- Evaluation, readback and conversion take the scope and, beside it, a
-- context the client supplies. The core is polymorphic in the context, and a
-- language states in its 'Eval' instance what it needs of it. A context may
-- give the free names of a language values ('definition', by default from
-- 'HasDefinitions'). Under a binder the language says what the context
-- learns ('extendScopedWith'). By default the binder only adds its names, so
-- any 'Foil.Sinkable' context works with any language. The demonstration
-- languages use 'NoContext', which knows nothing beyond the scope.
--
-- A language specialises 'nf', 'eval' and 'quote' to its types, next to
-- its 'Eval' instance, keeping the scope polymorphic and fixing the context
-- to 'NoContext':
--
-- > type Term n = AST Pattern TermSig n
-- > type Value n = NbE.Value Pattern TermSig n
-- >
-- > {-# SPECIALIZE NbE.nf    :: Distinct n => Scope n -> NoContext n -> Term n -> Term n #-}
-- > {-# SPECIALIZE NbE.eval  :: (Distinct o, Distinct i) =>
-- >       Scope o -> NoContext o -> Substitution Value i o -> Term i -> Value o #-}
-- > {-# SPECIALIZE NbE.quote :: Distinct n => Scope n -> NoContext n -> Value n -> Term n #-}
--
-- and likewise 'FreeFoil.NbE.Conversion.conv' and
-- 'FreeFoil.NbE.Conversion.convertible'. Without the pragmas the monolithic
-- demonstration language is 1.25× to 1.4× slower: GHC's own specialisation
-- at a call site fixes the scope too, so it ends at the first binder, and it
-- never specialises the calls to 'eval' inside the instance.
--
-- A client with a context of its own gives the same pragmas at its context.
-- For them to reach the rules, the instance marks 'evalSig' @INLINABLE@,
-- and 'etaMatchWith' and 'extendScopedWith', if it gives them, @INLINE@.
-- Otherwise every node runs the unspecialised evaluator, and conversion and
-- readback build the nodes these two methods return. A helper of the
-- language that takes the context, such as lambda-pi's @appValue@, is
-- specialised only at the contexts of its own pragmas.
module FreeFoil.NbE
  ( -- * Semantic domain
    Value (..)
    -- * Context
  , NoContext (..)
  , HasDefinitions (..)
  , Extend (..)
  , sinkExtend
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

-- | The context that knows nothing beyond the scope.
data NoContext (n :: Foil.S) = NoContext

instance Foil.Sinkable NoContext where
  sinkabilityProof _ NoContext = NoContext

-- | The values a context gives to free names, the default of 'definition'.
-- 'NoContext' defines nothing. A language generic in the context requires
-- this class of it in its 'Eval' instance, which needs
-- @UndecidableInstances@.
class HasDefinitions ctx binder sig where
  -- | The value of a free name, or the name itself if the context does not
  -- define it.
  contextDefinition :: Foil.Scope n -> ctx n -> Foil.Name n -> Value binder sig n

instance HasDefinitions NoContext binder sig where
  {-# INLINE contextDefinition #-}
  contextDefinition _ _ = VVar

-- | The context under the binder of a scoped position: from the scope, the
-- binder, refreshed for the scope, the scope under it, which free-foil
-- computes when it refreshes the binder, and the context. A language gives
-- one for each scoped position of a node with 'extendScopedWith'. The
-- extension receives the language's 'Eval' instance from the core, so that
-- an instance whose extension evaluates does not refer to itself, and its
-- 'extendScopedWith' stays inlinable.
newtype Extend ctx binder sig n = Extend
  (forall l. (Eval ctx binder sig, Foil.Distinct n, Foil.DExt n l) =>
    Foil.Scope n -> binder n l -> Foil.Scope l -> ctx n -> ctx l)

-- | The context under a binder that adds nothing but its names: the same
-- context, sunk.
sinkExtend :: Foil.Sinkable ctx => Extend ctx binder sig n
{-# INLINE sinkExtend #-}
sinkExtend = Extend (\_ _ _ -> Foil.sink)

-- * η

-- | The observer of a term position of an introduction form: the eliminator
-- of that position, from the scope, the context and any value to the
-- component. The two observers of a pair are @fst@ and @snd@. Like an
-- 'Extend', an observer receives the language's 'Eval' instance from the
-- core.
newtype EtaTerm ctx binder sig n =
  EtaTerm (Eval ctx binder sig => Foil.Scope n -> ctx n -> Value binder sig n -> Value binder sig n)

-- | The observer of a scoped position of an introduction form: from the
-- context under the position's refreshed binder, that binder, and the other
-- value sunk into that scope, the eliminator applied to the names the binder
-- binds. The observer of a lambda's body applies the other value to the
-- bound name. The outer scope is distinct so that an observer may list the
-- binder's names.
newtype EtaScoped ctx binder sig n =
  EtaScoped
    (forall l. (Eval ctx binder sig, Foil.Distinct n, Foil.DExt n l) =>
      Foil.Scope l -> ctx l -> binder n l -> Value binder sig l -> Value binder sig l)

-- * Evaluation

-- | A language becomes an NbE instance by giving its elimination rules:
-- 'evalSig' receives a raw node and the environment, matches the
-- eliminators, evaluates the principal subterm and either reduces or, on a
-- neutral, rebuilds the node as a 'VNode'. Every other node falls through to
-- 'evalNode'. The node arrives raw so that a redex never builds the
-- interpreted node it would discard. The instance upholds the 'Value'
-- invariant; "LambdaPi" is a one-rule example. An instance comes with the
-- pragmas described in the module header.
class (Bifunctor sig, Bifoldable sig) => Eval ctx binder sig where
  -- | The value of a free name, or the name itself if it has none. By
  -- default the context's 'contextDefinition'.
  definition :: Foil.Scope n -> ctx n -> Foil.Name n -> Value binder sig n
  default definition :: HasDefinitions ctx binder sig => Foil.Scope n -> ctx n -> Foil.Name n -> Value binder sig n
  {-# INLINE definition #-}
  definition = contextDefinition

  evalSig ::
    (Foil.Distinct o, Foil.Distinct i) =>
    Foil.Scope o ->
    ctx o ->
    Foil.Substitution (Value binder sig) i o ->
    sig (ScopedAST binder sig i) (AST binder sig i) ->
    Value binder sig o
  evalSig = evalNode

  -- | The η law of an introduction form, for conversion checking, in the
  -- style of 'Data.ZipMatchK.zipMatchWith2':
  --
  -- > etaMatchWith _ term = \case
  -- >   PairSig a b -> Just (PairSig (term a (EtaTerm (\_ _ -> fstValue))) (term b (EtaTerm (\_ _ -> sndValue))))
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

  -- | The context under the binder of each scoped position of a node, for
  -- readback and conversion, in the style of 'etaMatchWith':
  --
  -- > extendScopedWith scoped term = \case
  -- >   PiSig dom body -> PiSig (term dom) (scoped body (Extend (\_ (PatternVar x) _ ctx -> assume x dom ctx)))
  -- >   …
  --
  -- The term positions are values, so that an extension may use them, such
  -- as the domain of a Π. By default every binder only adds its names
  -- ('sinkExtend'), which needs a 'Foil.Sinkable' context. A context that
  -- holds something for every name in scope, such as its type, is not
  -- sinkable, and a language that uses one gives this method. The method is
  -- @INLINE@, so that readback and conversion build no intermediate node.
  extendScopedWith ::
    Foil.Distinct n =>
    (a -> Extend ctx binder sig n -> c) ->
    (Value binder sig n -> d) ->
    sig a (Value binder sig n) ->
    sig c d
  default extendScopedWith ::
    (Foil.Sinkable ctx, Foil.Distinct n) =>
    (a -> Extend ctx binder sig n -> c) ->
    (Value binder sig n -> d) ->
    sig a (Value binder sig n) ->
    sig c d
  {-# INLINE extendScopedWith #-}
  extendScopedWith scoped term = bimap (\a -> scoped a sinkExtend) term

-- | Evaluate a term under an environment: look variables up, hand nodes to
-- 'evalSig'. A variable that the environment does not map is a free name,
-- which unfolds to its value if the context defines it and is a neutral
-- otherwise.
eval ::
  (Eval ctx binder sig, Foil.Distinct o, Foil.Distinct i) =>
  Foil.Scope o ->
  ctx o ->
  Foil.Substitution (Value binder sig) i o ->
  AST binder sig i ->
  Value binder sig o
{-# INLINABLE eval #-}
eval scope ctx !env = \case
  Var x -> case Foil.lookupSubst env x of
    VVar y -> definition scope ctx y
    v -> v
  Node node -> evalSig scope ctx env node

-- | Evaluate a node that has no elimination rule: suspend it whole under the
-- environment if it has scoped subterms, otherwise evaluate its term
-- subterms. The same environment both suspends the node and drives its
-- subterms. A node with no subterms of one kind is reused by coercion, which
-- requires the signature to be representational in both parameters; every
-- ordinary data type is.
evalNode ::
  (Eval ctx binder sig, Foil.Distinct o, Foil.Distinct i) =>
  Foil.Scope o ->
  ctx o ->
  Foil.Substitution (Value binder sig) i o ->
  sig (ScopedAST binder sig i) (AST binder sig i) ->
  Value binder sig o
{-# INLINE evalNode #-}
evalNode scope ctx env node =
  case ensureBivacuousFirst node of
    Just node' -> VNode (bimap absurd (eval scope ctx env) node')
    Nothing -> VSuspended env $ case ensureBivacuousSecond node of
      -- Nothing to evaluate either (a lambda, say): reuse the cell as it is.
      Just node' -> vacuous node'
      Nothing    -> bimap id (eval scope ctx env) node

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
  Foil.Scope n ->
  ctx n ->
  Value binder sig n ->
  AST binder sig n
{-# INLINABLE quote #-}
quote scope ctx = \case
  VVar x -> Var x
  VNode node -> Node $! bimap absurd (quote scope ctx) node
  VSuspended env node -> Node $! extendScopedWith (quoteScoped scope ctx env) (quote scope ctx) node

-- | Read back one scoped subterm of a suspended node: refresh the binder,
-- extend the context with the position's 'Extend' and the captured
-- environment with the binder, as a fresh neutral, evaluate the body once
-- under them, and quote the result. It inlines into 'quote', so it is
-- specialised with it.
quoteScoped ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  ctx n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  Extend ctx binder sig n ->
  ScopedAST binder sig n
{-# INLINE quoteScoped #-}
quoteScoped scope ctx env (ScopedAST binder body) (Extend extend) =
  Foil.withRefreshedPattern scope binder $ \extendEnv binder' scope' ->
    case Foil.assertDistinct binder of
      Foil.Distinct ->
        let ctx' = extend scope binder' scope' ctx
        in ScopedAST binder' (quote scope' ctx' (eval scope' ctx' (extendEnv env) body))

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
  Foil.Scope n ->
  ctx n ->
  AST binder sig n ->
  AST binder sig n
{-# INLINABLE nf #-}
nf scope ctx = quote scope ctx . eval scope ctx Foil.identitySubst

-- | Read back the head of a value only: quote its term subterms, which are
-- values already, and freeze its scoped subterms instead of normalising under
-- their binders.
quoteWhnf ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  ctx n ->
  Value binder sig n ->
  AST binder sig n
quoteWhnf scope ctx = \case
  VVar x -> Var x
  VNode node -> Node $ bimap absurd (quote scope ctx) node
  VSuspended env node -> Node $ bimap (freezeScoped scope ctx env) (quote scope ctx) node

-- | Freeze one scoped subterm of a suspended node without evaluating under
-- its binder: refresh the binder and substitute the captured environment,
-- quoted to terms, into the still-syntactic body. 'substitute' only renames,
-- so a redex under the binder survives.
freezeScoped ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.Distinct i, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  ctx n ->
  Foil.Substitution (Value binder sig) i n ->
  ScopedAST binder sig i ->
  ScopedAST binder sig n
freezeScoped scope ctx env (ScopedAST binder body) =
  Foil.withRefreshedPattern scope binder $ \extendSubst binder' scope' ->
    ScopedAST binder' (substitute scope' (extendSubst (quoteSubst scope ctx env)) body)

-- | Quote every value in an environment, turning it into a syntactic
-- substitution.
quoteSubst ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder) =>
  Foil.Scope n ->
  ctx n ->
  Foil.Substitution (Value binder sig) i n ->
  Foil.Substitution (AST binder sig) i n
quoteSubst scope ctx (Foil.UnsafeSubstitution m) =
  Foil.UnsafeSubstitution (IntMap.map (quote scope ctx) m)

-- | Weak-head normal form: evaluate, then read back the head only. Shares
-- 'eval' with 'nf'; 'quoteWhnf' does not go under binders, so a redex
-- under a lambda survives. Term positions are values already, so the two
-- readbacks differ only at scoped positions.
whnf ::
  (Eval ctx binder sig, Foil.Distinct n, Foil.CoSinkable binder, Foil.SinkableK binder) =>
  Foil.Scope n ->
  ctx n ->
  AST binder sig n ->
  AST binder sig n
whnf scope ctx = quoteWhnf scope ctx . eval scope ctx Foil.identitySubst
