# Design

This note says what the library does, what the entities are, what it
assumes, which decisions it rests on, and what is planned next. How
normalisation by evaluation works is not explained here; the references at
the end cover it.

## What it is

Normalisation by evaluation (NbE) splits a normaliser in two: an evaluator
from syntax into a semantic domain, and a readback from the domain into
syntax in normal form. Every language implementation writes this pair by
hand, for its own syntax and its own value type.

This library writes the pair once, for any language whose syntax is a
[free-foil](https://github.com/fizruk/free-foil) signature. A signature is
a bifunctor `sig scope term`, whose first parameter marks the positions that
bind a variable, together with a binder type; from these free-foil generates
the scope-safe term type `AST binder sig n`. A language supplies one
instance of a class with one method, its elimination rules. It gets the
semantic domain, evaluation, readback, and the normalisers `nfNbe` and
`whnfNbe`. The normaliser is untyped and intensional: it decides β and the
language's own reductions, not η, and it consults no types.

## What there is

- **The core**, `src/FreeFoil/NbE.hs`: the semantic domain `Value`, the `Eval`
  class, generic evaluation and readback, and the normalisers.
- **Three demonstration languages**, each one hand-written module with its
  `Eval` instance.
  - **lambda-pi**, `demo/LambdaPi.hs`: the untyped lambda calculus with the
    dependent function type as a term former. One rule, β.
  - **lambda-let**, `demo/LambdaLet.hs`: `let`, an eliminator that always
    fires. Example terms are in `demo/LambdaLet/Examples.hs`.
  - **Booleans**, `demo/Booleans.hs`: `if` on `true` and `false`, no binders.
    It shows that the core is generic in the signature.

  lambda-pi and lambda-let also have a BNFC grammar, the generated scope-safe
  syntax, a parser so that terms are string literals, and a substitution-based
  reference normaliser for the tests. Booleans is a signature written by hand
  and has none of these.
- **A monomorphic baseline**, `demo/LambdaPi/Monomorphic.hs`: a hand-written
  NbE for lambda-pi with one constructor per value form, over the same
  syntax. It measures what the generic value domain costs.
- **Tests**, 79 of them: β, normalisation under binders, `Pi`, neutrals,
  weak-head normal forms, parser round trips, value inspection, Booleans and
  lambda-let. Properties compare `nfNbe` and `nfMono` with the reference
  normaliser on random closed and open terms.
- **Benchmarks.** `nbe-bench` runs Church arithmetic, nested redexes, nested
  `let` and nested `Pi`. The lambda-n-ways harness under `bench/lambda-n-ways`
  compares the generic normaliser, the monomorphic baseline and a hand-written
  foil NbE on Weirich's corpus; `medians.sh` runs the measurement protocol.
  The numbers, and the series of changes behind them, are in the two
  benchmark READMEs.

The paper in preparation covers exactly this: the core, the three languages,
and the performance analysis. Everything under "What is planned" is future
work there.

## Interface

### The core

The module exports ten names.

- `Value binder sig n`: the semantic domain. A value is a term of the same
  signature whose term positions have been evaluated.
  - `VVar`: a neutral variable.
  - `VNode`: a node with no scoped positions; its term positions hold
    values. A stuck eliminator is a `VNode`.
  - `VSuspended`: a node with scoped positions, suspended as a whole. Its
    term positions hold values, its scoped positions hold the original
    syntax, and one captured environment serves all of them. A lambda is a
    `VSuspended`; so is a dependent function type, with its domain evaluated
    and its codomain waiting.
- `Eval binder sig`: the class a language instantiates. Its one method,
  `evalSig`, receives a raw syntax node and the environment and returns a
  value. The instance matches its eliminators and either reduces or rebuilds
  a neutral; every other node falls through to the default.
- `eval scope env term`: evaluates a term under an environment, a free-foil
  `Substitution` with values as its codomain. A variable the environment
  does not bind is a neutral.
- `evalNode`: the default of `evalSig`. It evaluates the term positions of a
  node and suspends the node if it has scoped positions.
- `quote scope value`: reads a value back into a term in normal form.
- `quoteSuspendedScoped`: reads back one scoped position of a suspended
  node. Exported so that a language can specialise it.
- `nfNbe scope term`: `quote` after `eval`. The normal form.
- `quoteWhnf scope value`: reads back the head of a value only.
- `freezeSuspendedScoped`: the scoped-position step of `quoteWhnf`. It
  substitutes the environment into the body instead of evaluating it.
- `whnfNbe scope term`: `quoteWhnf` after `eval`. The weak-head normal form.

A language must satisfy these constraints. Its signature is a `Bifunctor`
and a `Bifoldable`; both can be derived. Its binder type is `CoSinkable` and
`HasNameBinders`, and `SinkableK` for `whnfNbe`; free-foil generates the
first and has generic defaults for the other two. It writes one `Eval`
instance. It should also add `SPECIALIZE`
pragmas for `nfNbe`, `eval`, `quote` and `quoteSuspendedScoped` at its
signature, as `demo/LambdaPi.hs` does; without them the loop passes class
dictionaries at run time.

### The demonstration languages

| Module | What it exports |
|---|---|
| `LambdaPi`, `LambdaLet` | The term type, pattern synonyms (`Var`, `App`, `Lam`, and `Pi` or `Let`), the `Eval` instance, `Value`, the inherited `eval`, `nfNbe` and `whnfNbe`, and the reference `nf` and `whnf`. `LambdaPi` also exports the example terms `two`, `appTwo` and `neutralNbeOk`. |
| `Booleans` | The signature `BoolSig`, the term type, the patterns `TT`, `FF` and `If`, and `nf`. |
| `LambdaPi.Parser`, `LambdaLet.Parser` | `parseLambdaPi` or `parseLambdaLet` for closed terms, `parseOpen` for terms in a scope, `withFreeVars` to build such a scope, and the `IsString` instance. |
| `LambdaPi.PrettyPrint` | `ppValue`, which quotes a value and prints the term, and `ppValueStruct`, which prints the value's structure; the latter is also `show`. |
| `LambdaPi.Monomorphic` | The value type `Val`, `eval`, `quote` and `nfMono`. |
| `LambdaPi.LambdaNWays` | The bridge to the lambda-n-ways harness: the mirrored `LC` and `IdInt` types, the conversions `fromLC` and `toLC`, the normalisers `nbeNf`, `monoNf` and `refNf`, and `aeq`. |
| `LambdaLet.Examples` | Six terms that show what `let` does, and the list `examples`. |
| `<Lang>.Raw`, `<Lang>.Generated` | The raw syntax from BNFC with the free-foil configuration, and the generated scope-safe syntax: the signature, the term type, the `FF`-prefixed pattern synonyms, and the conversions `toTerm` and `fromTerm`. |

## Assumptions

These are the library's own. What free-foil requires of scopes, binders and
patterns is not repeated here.

- **The instance upholds the invariant.** The language's `evalSig` never
  returns an eliminator applied to the introduction form it eliminates.
  Nothing checks this for a new language; see the decision "Weak-head
  normality as an invariant".
- **The signature is representational in both parameters.** `evalNode`
  reuses a node's heap cell at another type by coercion when the node has no
  subterms of one kind. This holds for every ordinary data type. A signature
  that puts a parameter under a type family or in the argument position of a
  function would break it.
- **Terms may diverge.** The languages are untyped, so normalisation need
  not terminate. The tests force each normal form under a one-second budget
  and discard a case only when the reference normaliser diverges too.
- **Only single-variable binders are exercised.** The core is written for any
  free-foil pattern, but the three languages bind one variable at a time, and
  no test covers patterns with several.
- **Readback does not α-normalise.** Variables are named by their foil
  identifiers, so the printed form re-parses but two α-equivalent normal
  forms need not print the same. Normal forms are compared with
  `alphaEquiv`, as the tests do.

## Decisions

Each decision is recorded in four lines: the decision and the reason for
it, what it was chosen instead of, what it costs, and what would make us
revisit it. Where a property rests on a test or an invariant rather than on
the types, the cost line says so.

### One signature for terms and values

- **Decision.** Values are built over the same signature as terms. An
  intensional language then needs no second signature and no injection; one
  instance, and everything else is inherited.
- **Instead of.** A separate value signature, `EvalTo sigT sigV`, with the
  term signature injected into it by default. Extensional sums need it,
  because their values have formers the syntax lacks.
- **Cost.** The type does not keep eliminators out of values:
  `VSuspended env (LetSig e body)` is a well-typed value of lambda-let. That
  `eval` never builds one is a fact about the evaluator, guarded by the
  `letUnused` test, not by the type. The split would add an injection back
  for readback, dispatch over a signature sum on the value side, and an
  unmeasured effect on speed.
- **Revisit when.** Extensional booleans or sums enter the zoo, or the
  planned experiment shows the split costs nothing on intensional languages.

### Eager values, whole-node suspension

- **Decision.** Term positions are evaluated when a node is reached; scoped
  positions are suspended as syntax under one environment per node. Readback
  then visits each subterm once and is linear in the size of the term. The
  test "deep Pi nesting stays linear" and the `Nested Pi types` benchmark
  guard this: 14, 71 and 146 µs at depths 100, 500 and 1000.
- **Instead of.** Suspending a whole node under one environment, as the first
  version did: it normalised a `Pi` codomain twice and was exponential in the
  nesting depth, 2.7 s and 4.6 GB at depth 18. Or one closure per binder,
  `VLam env body`, as in most hand-written NbE implementations; the
  monomorphic baseline uses it.
- **Cost.** None for correctness. A generic node is a constructor box around
  a signature cell, so a value is one heap object more than in the
  monomorphic baseline.
- **Revisit when.** Only for performance: the single-type representation in
  [issue #7](https://github.com/p50000/free-foil-NBE/issues/7).

### Call-by-need environments

- **Decision.** An argument, or a `let`-bound expression, enters the
  environment as a thunk: evaluated at most once, on first use, and never if
  unused. This is the host language's evaluation order and costs nothing to
  obtain; the `letUnused` and `letSharing` tests pin it down.
- **Instead of.** Call-by-value, which forces on extension; or call-by-name,
  which is what the substitution-based reference normaliser does.
- **Cost.** A thunk per binding until its first use. Call-by-value would
  evaluate unused arguments and diverge on an unused Ω. Call-by-name repeats
  the work at every use; the `Nested let` benchmark puts the factor at about
  6000 at depth 1000.
- **Revisit when.** A profile attributes a large share of allocation to
  environment thunks on a realistic corpus.

### Weak-head normality as an invariant

- **Decision.** Every value `eval` produces is weak-head normal at every
  position: no node is an eliminator applied to the introduction form it
  eliminates. Neutral values are not a separate type. The language's
  `evalSig` establishes the invariant, the generic functions preserve it, and
  the property tests check it against the reference normaliser.
- **Instead of.** Separate neutral and normal types, with a neutral as a head
  and a spine of arguments: a static guarantee, constant-time access to head
  and spine, and the shape that glued evaluation and spine-wise conversion
  checking need.
- **Cost.** Nothing checks the invariant for a new language. A neutral's
  spine is a chain of nodes rather than a head with a list. The split would
  cost each language a classification of its constructors, as two signatures
  or as a class marking the eliminators.
- **Revisit when.** Conversion checking starts and wants the head-and-spine
  shape.

### Untyped, intensional readback

- **Decision.** Normal forms are β-normal, with the language's own
  reductions; readback consults no types, and there is no type checker.
  `\f. \x. f x` and `\f. f` are different normal forms. Every intensional
  feature needs no types, and the user obligation stays at one instance.
- **Instead of.** A type-directed readback that takes a semantic type. It
  decides η for functions, records and unit, and it is the way to extensional
  sums.
- **Cost.** No η. The typed readback needs types as values in the domain and
  a typing discipline for each language that wants it.
- **Revisit when.** The next planned step adds the typed readback as an
  opt-in, with η for functions in lambda-pi; the untyped one stays the
  default.

### Values are data, not host-language closures

- **Decision.** A value is a data structure over the signature; a binder body
  is kept as syntax with its environment, never as a Haskell function. Data
  can be inspected, printed, substituted into and compared, which conversion
  checking, glued evaluation and unification all need. `ppValueStruct`
  prints a value's suspended bodies and their environments.
- **Instead of.** Higher-order abstract syntax: a binder body as a function
  from values to values, with scope handling left to the host run time, as in
  Boespflug's untyped NbE.
- **Cost.** Speed. Boespflug's evaluator runs within a few percent of the
  host evaluator; this one pays for environments and binder refresh. In
  return the value domain is open: a new constructor needs no recompilation
  of the evaluator.
- **Revisit when.** Not planned. The rest of the design is built on this.

### Names and scopes from foil

- **Decision.** Values name variables with foil names in a phantom scope, as
  terms do; readback refreshes a binder with `withRefreshedPattern`; sinking
  a value into a larger scope is a coercion. The normaliser has no binder
  bookkeeping of its own: free-foil owns scope handling for terms and values
  alike, and its distinction between renaming and substitution matches the
  fact that normal forms are stable under renaming but not under
  substitution.
- **Instead of.** De Bruijn levels in values and indices in terms, converted
  at readback, as in Kovács's implementations: constant-time quoting with no
  refresh.
- **Cost.** Binder refresh at readback through the pattern-generic
  `withRefreshedPattern`. Before free-foil's scoped traversals it was about
  15% of the time on the random corpora; after them it is no longer the
  first item, see the analysis in
  [issue #3](https://github.com/p50000/free-foil-NBE/issues/3). Levels would
  need a second representation and a conversion at the boundary, outside
  what free-foil generates.
- **Revisit when.** A profile shows binder refresh dominating readback.

### The raw-node contract of `evalSig`

- **Decision.** An eliminator receives the raw syntax node and the
  environment, evaluates its own principal subterm, and reduces or rebuilds a
  neutral; introduction forms fall through to the default. A redex never
  pays for an interpreted node it discards: 28% of the time and 29% of the
  allocation on the factorial benchmark. An eliminator with a binding branch,
  such as `case`, needs no framework support either: it evaluates the branch
  under an extended environment, as β enters a lambda body.
- **Instead of.** A pre-interpreted node whose term positions are values and
  whose scoped positions are closures, so that the instance contains no
  explicit evaluation calls.
- **Cost.** The instance evaluates its subterms itself, and can forget to.
- **Revisit when.** No trigger known.

### Specialisation at the language boundary

- **Decision.** The generic loop is `INLINABLE`, and a language adds
  `SPECIALIZE` pragmas for `nfNbe`, `eval`, `quote` and
  `quoteSuspendedScoped` at its signature, as `demo/LambdaPi.hs` does.
  Without them the loop passes class dictionaries at run time, and the
  `nfNbe` pragma alone does not reach the inner functions. Full
  specialisation was worth 12% to 18% of the time.
- **Instead of.** Generating the pragmas with Template Haskell next to the
  syntax, or generating a monomorphic normaliser outright. The monomorphic
  baseline bounds the second: the generic domain costs 1.25× on the
  factorial term and 1.4× on the random corpora on top of it.
- **Cost.** Four pragmas per language that nothing checks for. The readback
  wrapper is still not fully specialised; a scratch build that fixes this
  brings generic against monomorphic to about 1.15×.
- **Revisit when.** The wrapper fix is ready, or languages forget the pragmas
  often enough to want them generated.

### Eliminators that always fire

- **Decision.** `let x = e in b` is an eliminator with no stuck case: it
  evaluates `b` under the environment extended with `e`, as β enters a
  lambda body, and never appears in a value or a normal form. It is the
  smallest feature past functions, needs no change to readback, and shows
  sharing, which substitution cannot; see the `Nested let` benchmark.
- **Instead of.** `let` as sugar for an application, which loses nothing and
  keeps the syntax smaller; or a value signature without `let`, which makes
  its absence from values a fact of the type.
- **Cost.** Its absence from values is not a fact of the type, as recorded
  under "One signature for terms and values".
- **Revisit when.** Other eliminators of this shape are added, such as a type
  ascription `(e : A)` that evaluation erases or an explicit substitution
  node. The two-signature experiment will measure whether keeping them out
  of values costs or saves time.

### Weak-head normal forms under eager values

- **Decision.** `whnfNbe` shares `eval` with `nfNbe` and differs in readback
  only: scoped positions are frozen, with the binder refreshed and the
  environment substituted into the body as syntax. One evaluator serves both
  normalisers, and weak-head normalisation is "readback stops at binders";
  see the `whnfNbe` tests and the `letUnderLam` example.
- **Instead of.** A lazy evaluator in which the arguments of a neutral stay
  unevaluated, the textbook weak-head normal form.
- **Cost.** Term positions are values already, so the arguments of a neutral
  come out normalised: more work than a textbook weak-head normal form on a
  stuck term.
- **Revisit when.** Conversion checking needs to compare heads without
  evaluating arguments, which needs lazy term positions, the glued or spine
  representation.

## What is planned

In the order we intend to build it. Each step is one pull request with the
implementation, an example and its documentation.

1. **Typed readback and η for functions.** An opt-in readback that takes a
   semantic type; the untyped one stays the default. First payoff: η for
   functions in lambda-pi, where `Pi` is already a value.
2. **Products and Σ**, with η for pairs on the same readback.
3. **Two signatures.** A value signature distinct from the term signature,
   `EvalTo sigT sigV`, with the term signature injected by default. Before
   it, an experiment on lambda-let: does a value signature without `let` cost
   or save time against the single signature?
4. **Extensional booleans**, the first language whose value domain has
   formers its syntax lacks, and the road to extensional sums.
5. **Universes**: types as values in general.
6. **Conversion checking** as an operation of its own. Compare weak-head
   values spine-wise, and unfold definitions only when the spines disagree,
   which is glued evaluation. Today two terms are normalised and compared
   with `alphaEquiv`.
7. **Metavariables and pattern unification**, on top of conversion checking.

Off the critical path, as further demonstration languages when useful:
naturals with a recursor, and products and sums by their β rules alone.

Two open performance items from review, neither scheduled.
[#3](https://github.com/p50000/free-foil-NBE/issues/3): a shortcut for
subterms that contain no redex, where the generic normaliser is about 6×
slower than a single structural pass.
[#7](https://github.com/p50000/free-foil-NBE/issues/7): a single-type
representation of syntax and values.

## Where to read how it works

The evaluate-then-quote structure follows
[Christiansen's tutorial](https://davidchristiansen.dk/tutorials/nbe/). The
eager-values domain with one suspension point per binder is the shape of
Kovács's [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
and [smalltt](https://github.com/AndrasKovacs/smalltt); the monomorphic
baseline is a direct instance of it. Allais, Atkey, Chapman, McBride and
McKinna, [A type and scope safe universe of syntaxes with
binding](https://doi.org/10.1145/3236785), give the one earlier
signature-generic NbE, in Agda. Boespflug's [Efficient normalization by
evaluation](https://inria.hal.science/inria-00434283) is the host-closure
design this library does not take. The
[Free Foil paper](https://arxiv.org/abs/2405.16384) sketched the generic
closure that this library realises.
