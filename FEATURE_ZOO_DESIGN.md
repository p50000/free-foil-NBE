# Language features and term operations: a design plan

This note maps the design space of the framework along two axes:

- **Features** — the object-language constructors with their normalisation
  rules: from functions and booleans through sums and universes to the
  research horizon of extension types (rzk), refinement types, and cubical
  primitives.
- **Operations** — what one *does* with terms: normalise and store, check
  conversion, unify, anti-unify — and how each relates to NbE.

For each feature we record *how* it is realised via normalisation by
evaluation (NbE). It is a design plan: some features are implemented, most are
planned. Two of them depend on framework extensions whose design directions
are now fixed (Decisions A and B below); those are called out explicitly. The two axes meet in the
[design-space map](#the-design-space-map-features--operations) at the end — a
table of what exists in the space (with literature per cell) and what we
support at which stage.

Two features are already implemented and serve as templates:

- **Functions** (`demo/LambdaPi.hs`) — `Lam`/`Pi` are introductions with a bound
  (`scope`) position; `App` is the one eliminator (β), stuck on a neutral head.
- **Booleans** (`demo/Booleans.hs`) — `true`/`false` introductions, `if`
  eliminator, stuck on a neutral condition; no binders.

Everything else below is planned.

## The organising idea: intensional (β) vs extensional (β + η)

The whole feature zoo splits on a single line:

- **Intensional NbE (β only).** Reduce each eliminator on canonical values, leave
  it stuck on neutrals. This is what the framework does today, and **the entire
  zoo is reachable this way with no new machinery** — one value signature
  (`sigV = sigT`), untyped `quote`, and one `evalSig` per language. Functions,
  booleans, naturals, let, products, and sums all fit.
- **Extensional NbE (β + η).** Additionally decide the η-laws (`f = λx. f x`;
  `p = (fst p, snd p)`; sum commuting conversions). η is *type-directed*, so it
  needs a typed readback (**Decision B**); the sum case additionally needs the
  value domain to carry formers absent from the syntax (**Decision A**).

The two framework decisions are therefore exactly the price of
extensionality. A natural staging would build the intensional zoo first; the
design review chose instead to take one intensional step (let) and then head
straight for the extensional frontier, leaving the remaining intensional
features as fill-ins (see the [build order](#the-agreed-build-order)).

## The second axis: what we do with terms

Normalisation is only one of the operations a type-theory implementation needs.
Four form a natural ladder, and all four relate to NbE — but differently. In
one line: *normalisation **is** NbE; conversion is NbE minus quote; unification
is conversion plus solving, with readback constructing the solutions;
anti-unification shares unification's pattern fragment and uses NbE as a
preprocessor.*

### Normalise (and store)

Compute β(η)-normal forms and keep them — for display, for caching, for
comparing later. This is NbE proper: `eval` into the value domain, `quote` back
to syntax (`nfNbe`), or stop at the head (`whnfNbe`). **Implemented.** Storage
concerns (memoisation of quoting, hash-consing) are opt-in optimisations on
top. Literature: [BS91], [Chr], [Abe13]; on the performance of untyped
normalisation, [Boe09].

### Conversion checking

Decide `t ≡ u` *without* fully normalising either side: evaluate both to
weak-head values, compare heads, recurse spine-wise on neutrals, apply η on the
fly where the type demands it. This is NbE-native — the comparison happens in
the value domain, so it is "NbE minus quote" — and asymptotically better than
normalise-then-α-compare on large stuck terms. Definitions are handled by
*glued evaluation*: a defined head unfolds only when the spines disagree.
**Planned** (the conversion strand, after the intensional zoo); today we do
`nfNbe` + α-equivalence as a stand-in. Literature: [Coq96], [AC07], [AÖV18],
[Kov], [rzk346].

### Unification

Given metavariables, find a substitution making the two sides convertible. The
NbE connection is structural, not incidental: flex/rigid analysis happens on
*weak-head values* (unification is driven by the evaluator), and in the Miller
pattern fragment `?m x₁ … xₙ ≈ v` the solution is built by *readback* —
quoting `v` with the spine variables mapped to fresh binders is exactly our
`quote` at a renaming. Practical solvers also lean on approximate/glued
conversion to avoid unfolding. On free-foil specifically,
[`free-foil-hou`](https://github.com/fedor-ivn/free-foil-hou) already
implements signature-generic Huet-style preunification *without* NbE; marrying
it with this evaluator is the natural plan. **Planned** (metavariable stage).
Literature: [Hue75], [Mil91], [AP11], [Nor07], [Kov].

### Anti-unification (generalisation)

The dual of unification: find the *least general generalisation* of two terms,
replacing disagreeing subterms by fresh variables. The NbE relevance is real
but thinner: (i) anti-unify *normal forms* — NbE as preprocessing, so that
β-noise does not block generalisation (generalisation modulo βη); (ii)
higher-order *pattern* anti-unification is decidable with a unique lgg and
reuses the same pattern fragment as unification, hence the same spine/readback
machinery. **Out of scope** (confirmed at the design review) — recorded here as
open space; the pattern machinery of the metavariable stage would be its
foundation if it is ever picked up. Literature:
[Plo70], [Rey70], [Pfe91], [BKLV17], [CK23].

Further variations — matching (one-sided unification), subtyping-as-entailment
(refinements, topes), equality modulo definitions — are restrictions or
extensions of these four and inherit their NbE story.

## The recipe — six slots per feature

For each feature we record:

1. **Signature extension** — the new constructors on the bifunctor
   `sig scope term` (which positions bind = `scope`, which are `term`).
2. **Eliminators** — which constructors are elimination forms (the `evalSig`
   cases); introductions need none (the generic default rebuilds them).
3. **Reduction rules** — how each eliminator fires on a canonical principal
   value.
4. **Stuck / neutral** — the eliminator on a neutral (variable-headed) principal
   rebuilds a neutral node.
5. **Quoting** — inherited by default; *type-directed* only for η.
6. **Framework need** — none / heterogeneous values (Decision A) / typed
   readback (Decision B).

A note on the `evalSig` contract, as it stands after the performance series:
an eliminator receives the **raw** syntax node together with the current
environment, evaluates its own principal subterm, and either reduces or
rebuilds a neutral; introduction forms fall through to the generic default,
which suspends the node whole under the environment. One pleasant consequence:
an eliminator with a *binding* branch (`caseNat`, `case`) needs no framework
extension at all — it evaluates the branch under an extended environment
exactly as β evaluates a lambda body. (An earlier revision of this plan listed
"a binder inside an eliminator" as a framework need; the raw-node contract
dissolved it.)

## Planned features

### Let / definitions — intensional, no framework change

1. **Signature.** `LetSig term (x. term)` — a bound expression (term) and a body
   binding `x` (scope). Top-level definitions are the same idea with a global
   environment.
2. **Eliminator.** `LetSig` behaves like a cut — it always reduces.
3. **Reduction.** `let x = e in b` evaluates `b` under the environment extended
   by `x ↦ eval e`; structurally identical to β, but the redex is always present.
4. **Neutral.** None — `let` never gets stuck.
5. **Quoting.** Inherited.
6. **Framework need.** None for local `let`. Top-level definitions with *lazy
   unfolding* are best served by glued evaluation (a definition is a neutral head
   that unfolds on demand); the operation that needs this is conversion checking
   rather than normalisation.

### Naturals — intensional, no framework change

The first feature past booleans: a value-carrying introduction (`suc`) and a
recursive eliminator.

1. **Signature.** `ZeroSig | SucSig term | RecSig term term term` (base, step,
   target). A `CaseNat target zBranch (p. sBranch)` variant binds the
   predecessor.
2. **Eliminator.** `RecSig` (or `CaseNat`).
3. **Reduction.** `rec b s zero → b`; `rec b s (suc n) → s n (rec b s n)` (the
   step is applied, so this composes with the function fragment). `caseNat` binds
   the predecessor: `caseNat (suc m) z (p. s) → eval s under env[p ↦ m]`.
4. **Stuck.** Neutral target rebuilds a neutral eliminator.
5. **Quoting.** Inherited.
6. **Framework need.** None. `caseNat` is the first **binding eliminator**
   and a useful template in its own right, but under the raw-node `evalSig`
   contract it costs nothing extra: the branch is evaluated under `env[p ↦ m]`
   exactly as β evaluates a lambda body.

### Products / Σ — β needs nothing; η needs Decision B

1. **Signature.** `PairSig term term`, **`FstSig term`**, **`SndSig term`**; the
   dependent type former `SigmaSig term (x. term)` (like `Pi`).
2. **Eliminators.** `Fst`, `Snd`.
3. **Reduction.** `fst (pair a b) → a`; `snd (pair a b) → b`.
4. **Stuck.** Projection of a neutral rebuilds a neutral projection.
5. **Quoting.** β inherited; **η** (`p = (fst p, snd p)`) is type-directed.
6. **Framework need.** β none; η needs typed readback (Decision B).

### Sums / coproducts — β needs nothing; extensional needs A + B

1. **Signature.** `InlSig term`, `InrSig term`,
   **`CaseSig term (x. term) (y. term)`** (two binding branches).
2. **Eliminator.** `Case`.
3. **Reduction.** `case (inl a) (x. l) (y. r) → l[x ↦ a]`; `inr` symmetric.
4. **Stuck.** Neutral scrutinee rebuilds a neutral `case` — the *intensional*
   answer, buildable now (structurally a two-branch `caseNat`).
5. **Quoting.** Intensional inherited; the **extensional** theory (commuting
   conversions and sum-η; Altenkirch, Dybjer, Hofmann, and Scott) is
   type-directed *and* needs the value domain to represent a neutral that will
   resolve to `inl`/`inr`.
6. **Framework need.** β none; extensional needs heterogeneous values
   (Decision A) and typed readback (Decision B). This is the acid test for both.

### Universes / types-as-values — enables typed readback

A universe `U` together with the type formers (`Pi`, `Sigma`, `Bool`, `Nat`, …)
as **values** in the semantic domain — they already evaluate to nodes. This is
where types enter *organically*: the semantic type a typed readback consults is
just another value. In the agreed order the typed readback (Decision B)
arrives *first*, piggybacking on lambda-pi's existing `Pi` values; the
universe then closes the loop, making types-as-values general rather than
being a prerequisite. (The formers themselves cost nothing intensionally —
the row sits at the extensional frontier because its payoff is the typed
readback it generalises.)

### η (functions, records, unit) — the extensional frontier

Type-directed expansion at quote time: at `A → B`, a value `f` reads back as
`λx. quote (app f x)` (quoting the body at type `B`); at `Σ`, `p` reads back as
`(quote (fst p), quote (snd p))`; at unit, everything reads back as `()`. This is
the first consumer of the typed readback.

## Research horizon: features from rzk and Cubical Agda

Beyond the zoo above lie the constructors of real proof assistants. We walk
through rzk and Cubical Agda and record, per feature, what NbE-shape it has and
what *new framework slots* it would demand. None of these are scheduled; they
are the stress tests the framework should eventually face, and each one
teaches us a requirement worth knowing early. The horizon does have a concrete
long-term application target: ideally this framework's normaliser eventually
backs rzk's own evaluation, which is why the rzk-shaped rows (extension types,
topes) head the list.

### Extension types (rzk)

Riehl–Shulman extension types [RS17]: functions out of a *shape* whose values
are **judgmentally** constrained on a sub-shape — `⟨(t : I | ψ) → A [φ ↦ a]⟩`
denotes maps that are *definitionally* equal to `a` wherever the tope `φ`
holds. NbE-wise ([rzk346] is the reference implementation):

- **Signature.** A second sort of variables (shape/tope layer) next to term
  variables; type former carries the constraint `[φ ↦ a]`.
- **Reduction.** Application reduces to `a` whenever the argument
  *provably* lies in `φ` — so an `evalSig` case fires depending on a
  **semantic side-condition** (tope entailment, decided by a solver), not just
  on the head constructor of the principal value. That is a genuinely new slot
  in our recipe.
- **Stuck.** Neutral applications carry the pending constraint; conversion
  consults the tope solver.
- **Framework need.** Multi-sorted binders (free-foil's pattern generality is
  the candidate mechanism) + solver-guarded reduction + typed readback.

### Refinement types

`{x : A | p}` with SMT-discharged entailment (Liquid Types [RKJ08], LiquidHaskell
[Vaz14], F* [Swa16] — whose own normaliser is NbE-based). The instructive
point: **normalisation is untouched** — terms of refinement type normalise as
terms of `A` (refinement erasure). All the action is in *conversion*, which
becomes subtyping-with-entailment delegated to a solver; NbE's role is to
normalise terms before encoding them for the solver. Structurally this is the
same shape as rzk's tope layer: a designated logical fragment discharged by a
decision procedure, while NbE handles the λ-fragment. Framework need: none for
normalisation; a solver hook in the conversion operation.

### Cubical primitives (interval, systems, Kan operations)

CCHM / Cubical Agda [CCHM], [VMA19]. The interval `𝕀` with its de Morgan
structure introduces *interval variables* — again a second binder sort;
partial elements / systems `[φ ↦ a]` are constraint-guarded values (same slot
as extension types); and the Kan operations `transp`/`hcomp` reduce by
recursion on the **head of the type**, not of a term — an eliminator driven by
type structure, which presupposes types-as-values and typed evaluation
throughout. Normalisation for cubical type theory is settled in theory
[Hub16], [SA21] and practice (Cubical Agda, `cooltt`), and is the hardest
target on this map.

On the *performance* side the reference point is Kovács's `cctt` [cctt]: a
Cartesian cubical type theory "designed from ground-up with performance in
mind", computing Brunerie-number-style benchmarks that time out elsewhere. Its
key moves are NbE-adapted-to-the-interval — values support a cheap `sub`
operation that stores an interval substitution explicitly and shallowly, with
`force` computing head normal forms on demand — plus defunctionalised
closures (environment–term pairs, so substitution can act on them) and a
canonicity-based closed-evaluation optimisation for `hcom`. Defunctionalised
closures are the price of admission here: HOAS-style NbE with opaque
metalanguage closures normalises within a few percent of the host evaluator
[Boe09], but an opaque closure cannot be substituted into, compared
spine-wise, or glued — exactly the operations this row and the
conversion/unification columns need. The store-a-
substitution-in-the-value, force-on-demand shape is structurally kin to the
suspended-node representation our own performance series arrived at, which
suggests the framework's value domain is already pointed the right way for
this row.

### Modal types (context locks)

Multimodal type theory normalises via NbE [GSB19], [Gra22]. Interesting for us
for a different reason: locks modify *variable lookup* — precisely the part of
evaluation that languages normally inherit from the generic core — so modal
types perturb the framework itself rather than adding an `evalSig` case.
Recent work covers modal *dependent* types in one NbE proof [HJP23].

### Effects and handlers

A mature NbE line we should track: Moggi's computational λ-calculus [Fil01],
algebraic effects [AS13], and — recently — the first NbE algorithm for effect
handlers [SPB23]. Like locks, effects perturb the generic core rather than
adding an `evalSig` case: evaluation itself becomes monadic (a residualising
interpretation of the effect theory), so the framework question is whether
`eval` can be parametrised by a monad without taxing the pure languages.

## Framework decisions

Both decisions were reviewed and resolved in direction (design review,
September 2026); the candidate lists are kept for the record.

### Decision A — term signature vs value signature

Needed for **extensional sums** (and any value-only canonical or neutral
formers). Today the value and term signatures coincide. To let them differ, the
value domain is generalised over a value signature `sigV` while `eval` consumes
the term signature `sigT`; the crux is keeping readback `Value sigV → AST sigT`
total when `sigV` is richer. Candidate designs:

- a general `EvalTo sigT sigV` class (most general; readback for the extra
  constructors is a per-language obligation);
- an à-la-carte injection `sigV = sigT ⊕ (value-only formers)`, reusing
  free-foil's signature sum (keeps the generic core, makes the extra readback
  cases explicit and finite);
- a single signature with phase-marked constructors (least intrusive to the
  types, but muddies the bifunctor).

*Decided:* the general `EvalTo sigT sigV` class is the primary design — the
language author states how the two signatures relate, with a **default
implementation** covering the common case by injecting `sigT` into `sigV` (so
intensional languages, where the signatures coincide, cost no boilerplate).
The à-la-carte injection is demoted to an **opt-in** layering rather than the
default: in practice it forces case-dispatch over the signature sum onto the
value side, where we want a shared generic core with per-language value
differences layered separately. The phase-marked single signature is judged
unlikely to work at all and dropped. One action item precedes freezing the
API: review Sterling's synthetic Tait computability [Ste21] for structural
insight into the eval/readback interface.

The performance series has quietly moved the framework *toward* this split.
Since the raw-node contract, `evalSig` is already a map from the **term**
signature's raw nodes into the **value** domain — the two sides of the arrow
no longer mention the same functor application, so generalising the codomain
to a richer `sigV` is a change of type argument, not of architecture. And the
value-domain restructuring (now merged) goes further: values are no longer
"nodes of the term signature" at all, but split structurally into plain nodes
(scoped slots ruled out by type) and whole suspended nodes carrying their
environment. The value domain diverging from the syntax in a principled,
generic way is exactly the precedent Decision A needs.

### Decision B — typed vs untyped normalisation

η is type-directed, so it needs a readback that consults a semantic type:
readback indexed by a type value (with `Type = Value` once universes exist).
Candidate designs:

- keep untyped readback as the default and add a typed readback as an opt-in
  variant — intensional languages stay boilerplate-free; only η-wanting languages
  supply types;
- make readback typed throughout (type-directed NbE everywhere) — cleaner theory,
  but every language must provide a typing discipline;
- η-long neutrals without full types (functions only, arity-directed) — cheap but
  not general.

*Decided:* the opt-in typed variant, preserving the untyped intensional core.
Open sub-question: whether `Type` is a distinct index or simply `Value`.

## The agreed build order

Settled at the design review (September 2026), revising this document's
earlier suggestion: instead of completing the intensional zoo first, the
series takes one intensional step and heads for the extensional frontier.
The deliverable shape is a *series of small demo languages*, compact on
purpose — roughly four files each: the grammar, the free-foil generated code,
one hand-written file (the `Eval` instance and anything type-directed), and a
file of example terms. Each step is **one PR** and ships the trio:
implementation + example + documentation. (How later steps package their
syntax is an open comparison, to run before step 2: one self-contained
grammar per language, as in step 1, versus composing per-feature signatures
via free-foil's signature sum — the latter trades BNFC's concrete syntax for
reuse, and previews the machinery Decision A's opt-in à-la-carte layer needs
anyway.)

1. **Let / definitions** — intensional, no framework change.
2. **Types: η for functions** — the opt-in typed readback (Decision B) in the
   lambda-pi demo; `Pi` is already a value, so no universe is needed yet.
3. **Products and Σ** — with their type-directed η on the same readback.
4. **The signature split** — `EvalTo sigT sigV` (Decision A) with the default
   injection, preceded by the [Ste21] API review.
5. **Extensional booleans** — the first heterogeneous-value example (booleans
   as the two-constant coproduct); the road to extensional sums and records-η.
6. **Universes** — types-as-values made general (`U`, formers as values).
7. **Conversion checking** — glued evaluation + spine-wise algorithmic
   equality, replacing `nfNbe`-then-α-compare. A cross-cutting strand that can
   run alongside the series (η in conversion joins after step 2).
8. **Metavariables / pattern unification** — on top of 7, converging with
   `free-foil-hou`'s generic preunification. Anti-unification is out of scope,
   though it would fall out of the same pattern fragment.

Naturals and intensional products/sums drop off the critical path; their
recipes above remain as fill-in demos and templates (`CaseNat` stays the
binding-eliminator reference). Beyond the series, development steers by a
*target language*: rzk is the true target but genuinely hard, so a simpler
target comes first, and the horizon rows above map the approach.

## The design-space map (features × operations)

The two axes crossed. Each cell holds the key literature for that combination
(keys resolve in [References](#references)) and a stage marker saying when —
if at all — we plan to support it:

- ✅ implemented · **zoo** intensional (build step 1 and fill-in demos) ·
  **ext** build steps 2–6 (extensional, Decisions A/B) · **conv** step 7 ·
  **meta** step 8 · **hzn** research horizon · **open** no plan on our side,
  and mostly thin literature (cited where it exists) · — not applicable.

A cell's stage is the *later* of its row's feature stage and its column's
operation stage: e.g. conversion for sums needs both the conversion strand
(**conv**) and extensional sums (**ext**).

| Feature ↓ / Operation → | Normalise | Conversion | Unification | Anti-unification |
|---|---|---|---|---|
| Functions (λ/Π) | ✅ [BS91] [Chr] | **conv** [Coq96] [AC07] | **meta** [Hue75] [Mil91] [hou] | **open** [Pfe91] [BKLV17] |
| Booleans | ✅ [Chr] [AU04] | **conv** [AÖV18] | **meta** (rigid–rigid) | **open** [Plo70] [Rey70] |
| Naturals / recursors | **zoo** [Abe13] | **conv** [AÖV18] | **meta** | **open** |
| Let / definitions | **zoo** | **conv** glued [Kov] [rzk346] | **meta** [Kov] | — |
| Products / Σ | **zoo** (β) | **conv** (β); η: **ext** [AC07] | **meta** [AP11] | **open** |
| Sums / coproducts | **zoo** (β); ext.: [ADHS01] [BDF04] | **conv** (β); ext.: [ADHS01] [Lin07] [Sch17] | **open** | **open** |
| Universes | **ext** [Abe13] | **ext** [AÖV18] | **meta** [Kov] | — |
| η-laws (fn/record/unit) | **ext** [Abe13] | **ext** [AC07] | **meta** (patterns are η-long) [Mil91] | **open** |
| Extension types | **hzn** [RS17] [rzk346] | **hzn** topes [rzk346] | **open** | **open** |
| Refinement types | **hzn** (erasure) [RKJ08] [Swa16] | **hzn** SMT entailment [RKJ08] [Vaz14] | — (the solver's job) | **open** (liquid inference is lgg-flavoured) |
| Cubical (𝕀, Kan) | **hzn** [Hub16] [SA21] [VMA19] [cctt] | **hzn** [SA21] [cctt] | **open** | **open** |
| Modal (locks) | **hzn** [GSB19] [VRC22] [Gra22] [HJP23] | **hzn** [Gra22] | **open** | **open** |
| Effects / handlers | **hzn** [Fil01] [AS13] [SPB23] | **hzn** [SPB23] | **open** | **open** |

Two readings of the map. *Column-wise:* the Normalise column is our current
frontier; Conversion is one uniform strand (step 7) whose per-feature cost is
mostly inherited from the feature itself; Unification concentrates in the
pattern fragment; the Anti-unification column is almost entirely open space in
the literature — a fact worth knowing. *Row-wise:* the further down, the more
the feature perturbs the *framework* rather than adding an `evalSig` case —
side-condition-guarded reduction (extension types, systems), solver hooks
(refinements, topes), type-directed elimination (Kan), modified variable
lookup (locks).

## What prior work already covers (and what it does not)

A map like the one above looks like something the literature might already
contain, so we checked. It does not — but several works cover one slice each,
and three are close relatives that any write-up must discuss.

**Surveys and tutorials.** No general NbE survey crosses features with
operations. The canonical references each take one slice: Dybjer–Filinski
[DF02] (the standard tutorial: System T, βη, type-directed partial
evaluation), Berger–Eberl–Schwichtenberg [BES98] (survey chapter: higher-type
rewrite systems), Abel's habilitation [Abe13] (the dependent-types slice —
universes, irrelevance, impredicativity, *with* conversion checking), Danvy's
TDPE lecture notes [Dan99], and Christiansen's tutorial [Chr] (one fixed
dependently-typed language, normalise + convert, notably without sums).
Kovács's `elaboration-zoo` [Kov] is the only source treating normalisation,
conversion *and* unification together — but its features are elaboration
machinery (metavariables, implicits, pruning), not type formers.

**Generic and modular NbE.** Three lines come close on the framework side:

- Allais–Atkey–Chapman–McBride–McKinna [AACMM21] is, to our knowledge, the
  only prior *signature-generic* NbE implementation: NbE arises as an instance
  of their generic `Semantics` traversal over a universe of syntaxes. It is in
  Agda, explicitly unsafe (positivity checking disabled; partial,
  `Maybe`-valued results), demonstrated on one untyped instance, and covers
  only the normalise column.
- Valliappan's thesis *Modular normalization with types* [Val23] (with
  [VRL21], [VRC22]) is the best existing feature-axis review: one semantic
  recipe (possible-world models) instantiated across sums, effects, arrays,
  state, and Fitch-style modalities. It is simply-typed throughout,
  per-calculus rather than signature-generic, and normalise-only.
- The generic-metatheory line — gluing [KHS19], internal sconing [BKS23],
  synthetic Tait computability [Ste21], mode-theory-generic modal
  normalisation [Gra22], and Uemura's ∞-type-theoretic account [Uem22] —
  proves normalisation generically over signatures of whole type theories,
  but as mathematics, with no reusable implementation.

**Gap evidence.** Fiore–Szamozvancev's `agda-soas` [FS22] provides
signature-generic *metatheory* (substitution, metavariables, equational
reasoning) with no normalisation component — the nearest generic-syntax
ecosystem, with our column empty. Per feature, mature NbE lines exist for
effects ([Fil01]→[AS13]→[SPB23]), sums (closed off by [Sch17]), System F,
modal dependent types [HJP23], and — freshly — observational equality [SLK25];
genuinely uncovered are W-types / general recursors as a headline topic,
records / pattern matching, guarded and clocked theories, and (almost
entirely) the anti-unification column.

**A recurring technical obstruction** worth designing for early: normal forms
are stable under *renamings* but not under *substitutions* (observed
semantically by Fiore [Fio02]; stressed by Uemura [Uem22] as the reason a
substitution-stable generic framework cannot even state normalisation without
a two-mode renaming/substitution refinement). free-foil's built-in
renaming/substitution distinction is well-placed for exactly this — a point in
favour of the present representation.

**Theoretical anchor (ambitious).** The reason both the syntax *and* the
semantic domain are presented through signatures is that free-foil should own
all scope handling — the *second-order* presentation (signature with
designated binding positions, as in [FS22]), which we prefer to higher-order
abstract syntax. On the metatheory side, synthetic Tait computability [Ste21]
is the generalisation of NbE we would ideally align with: the ambition —
explicitly speculative — is to extract its central ideas as guidance for the
framework's API (starting with the eval/readback interface of Decision A),
not to mechanise the mathematics.

**Positioning.** The nearest relatives of this document are [Val23] (feature
axis, simply-typed, normalise-only), [Kov] (operations axis, one fixed
language), and [AACMM21] (signature axis, normalise-only, unsafe). No prior
work populates more than one cell of the features × operations map
generically; that intersection is what this framework targets.

## References

Keys as used in the map above.

**NbE and normalisation**

- [BS91] Ulrich Berger and Helmut Schwichtenberg. [*An inverse of the
  evaluation functional for typed lambda-calculus*](https://doi.org/10.1109/LICS.1991.151645)
  (LICS 1991) — the origin of NbE.
- [Chr] David Christiansen. [*Checking dependent types with normalisation by
  evaluation*](https://davidchristiansen.dk/tutorials/nbe/) (tutorial) — the
  evaluate-then-quote structure this framework follows.
- [Abe13] Andreas Abel. [*Normalization by evaluation: dependent types and
  impredicativity*](https://www.cse.chalmers.se/~abela/habil.pdf)
  (Habilitation, 2013) — type-directed NbE and η.
- [Boe09] Mathieu Boespflug. [*Efficient normalization by
  evaluation*](https://inria.hal.science/inria-00434283) (NbE Workshop,
  2009) — untyped HOAS-based NbE within a few percent of the host
  evaluator; eval/apply uncurrying and constructors-as-constructors (the
  2009 precedent of the raw-node dispatch lesson), at the cost of an opaque,
  closed-world value representation.

**Surveys and tutorials**

- [DF02] Peter Dybjer and Andrzej Filinski. [*Normalization and partial
  evaluation*](https://doi.org/10.1007/3-540-45699-6_4) (APPSEM 2000
  summer-school lecture notes, LNCS 2395, 2002).
- [BES98] Ulrich Berger, Matthias Eberl, and Helmut Schwichtenberg.
  [*Normalization by evaluation*](https://doi.org/10.1007/3-540-49254-2_4)
  (survey chapter, LNCS 1546, 1998) — NbE for higher-type rewrite systems.
- [Dan99] Olivier Danvy. [*Type-directed partial
  evaluation*](https://doi.org/10.1007/3-540-47018-2_16) (lecture notes,
  LNCS 1706, 1999).

**Generic and modular NbE**

- [AACMM21] Guillaume Allais, Robert Atkey, James Chapman, Conor McBride, and
  James McKinna. [*A type and scope safe universe of syntaxes with binding:
  their semantics and proofs*](https://doi.org/10.1145/3236785) (ICFP 2018;
  JFP 31, 2021) — generic NbE as an instance of a generic semantics traversal.
- [Val23] Nachiappan Valliappan. [*Modular normalization with
  types*](https://nachivpn.me/thesis.pdf) (PhD thesis, Chalmers, 2023).
- [VRL21] Nachiappan Valliappan, Alejandro Russo, and Sam Lindley. [*Practical
  normalization by evaluation for EDSLs*](https://doi.org/10.1145/3471874.3472983)
  (Haskell Symposium 2021).
- [VRC22] Nachiappan Valliappan, Fabian Ruch, and Carlos Tomé Cortiñas.
  [*Normalization for Fitch-style modal calculi*](https://doi.org/10.1145/3547649)
  (ICFP 2022).
- [Fio02] Marcelo Fiore. [*Semantic analysis of normalisation by evaluation for
  typed lambda calculus*](https://doi.org/10.1145/571157.571161) (PPDP 2002;
  journal version MSCS 32(8), 2022).
- [KHS19] Ambrus Kaposi, Simon Huber, and Christian Sattler. [*Gluing for type
  theory*](https://doi.org/10.4230/LIPIcs.FSCD.2019.25) (FSCD 2019).
- [BKS23] Rafaël Bocquet, Ambrus Kaposi, and Christian Sattler. [*For the
  metatheory of type theory, internal sconing is
  enough*](https://doi.org/10.4230/LIPIcs.FSCD.2023.18) (FSCD 2023).
- [Ste21] Jonathan Sterling. [*First steps in synthetic Tait
  computability*](https://www.jonmsterling.com/sterling-2021-thesis/) (PhD
  thesis, CMU, 2021).
- [Uem22] Taichi Uemura. [*Normalization and coherence for ∞-type
  theories*](https://arxiv.org/abs/2212.11764) (arXiv:2212.11764, 2022).
- [FS22] Marcelo Fiore and Dmitrij Szamozvancev. [*Formal metatheory of
  second-order abstract syntax*](https://doi.org/10.1145/3498715) (POPL 2022)
  — `agda-soas`; generic metatheory without a normalisation component.

**Conversion checking**

- [Coq96] Thierry Coquand. [*An algorithm for type-checking dependent
  types*](https://doi.org/10.1016/0167-6423(95)00021-6) (Sci. Comput.
  Program. 26, 1996) — conversion via weak-head forms.
- [AC07] Andreas Abel and Thierry Coquand. [*Untyped algorithmic equality for
  Martin-Löf's logical framework with surjective
  pairs*](https://www2.tcs.ifi.lmu.de/~abel/lfsigma.pdf) (Fund. Inf. 77(4),
  2007) — spine-wise equality, η for pairs.
- [AÖV18] Andreas Abel, Joakim Öhman, and Andrea Vezzosi. [*Decidability of
  conversion for type theory in type theory*](https://doi.org/10.1145/3158111)
  (POPL 2018).
- [Kov] András Kovács. [`smalltt`](https://github.com/AndrasKovacs/smalltt)
  and [`elaboration-zoo`](https://github.com/AndrasKovacs/elaboration-zoo) —
  glued evaluation, approximate conversion, metavariables in practice.
- [rzk346] Nikolai Kudasov.
  [`rzk-lang/rzk#346`](https://github.com/rzk-lang/rzk/pull/346) — glued
  neutral spines and spine-wise conversion in rzk's normaliser.

**Unification**

- [Hue75] Gérard Huet. [*A unification algorithm for typed
  λ-calculus*](https://doi.org/10.1016/0304-3975(75)90011-0)
  (Theor. Comput. Sci. 1(1), 1975).
- [Mil91] Dale Miller. [*A logic programming language with lambda-abstraction,
  function variables, and simple unification*](https://doi.org/10.1093/logcom/1.4.497)
  (J. Log. Comput. 1(4), 1991) — the pattern fragment.
- [AP11] Andreas Abel and Brigitte Pientka. [*Higher-order dynamic pattern
  unification for dependent types and records*](https://doi.org/10.1007/978-3-642-21691-6_5)
  (TLCA 2011).
- [Nor07] Ulf Norell. [*Towards a practical programming language based on
  dependent type theory*](https://www.cse.chalmers.se/~ulfn/papers/thesis.pdf)
  (PhD thesis, 2007) — metavariables in Agda.
- [hou] [`fedor-ivn/free-foil-hou`](https://github.com/fedor-ivn/free-foil-hou)
  — signature-generic Huet-style preunification on free-foil.

**Anti-unification**

- [Plo70] Gordon Plotkin. *A note on inductive generalization* (Machine
  Intelligence 5, 1970).
- [Rey70] John Reynolds. *Transformational systems and the algebraic structure
  of atomic formulas* (Machine Intelligence 5, 1970).
- [Pfe91] Frank Pfenning. *Unification and anti-unification in the Calculus of
  Constructions* (LICS 1991).
- [BKLV17] Alexander Baumgartner, Temur Kutsia, Jordi Levy, and Mateu Villaret.
  [*Higher-order pattern anti-unification in linear
  time*](https://doi.org/10.1007/s10817-016-9383-3) (J. Autom. Reasoning,
  2017).
- [CK23] David Cerna and Temur Kutsia. [*Anti-unification and generalization: a
  survey*](https://arxiv.org/abs/2302.00277) (IJCAI 2023).

**Sums and extensionality**

- [ADHS01] Thorsten Altenkirch, Peter Dybjer, Martin Hofmann, and Philip Scott.
  [*Normalization by evaluation for typed lambda calculus with
  coproducts*](https://doi.org/10.1109/LICS.2001.932506) (LICS 2001) — the
  subtlety behind extensional sums.
- [BDF04] Vincent Balat, Roberto Di Cosmo, and Marcelo Fiore. [*Extensional
  normalisation and type-directed partial evaluation for typed lambda calculus
  with sums*](https://doi.org/10.1145/964001.964007) (POPL 2004).
- [Lin07] Sam Lindley. *Extensional rewriting with sums* (TLCA 2007).
- [Sch17] Gabriel Scherer. [*Deciding equivalence with sums and the empty
  type*](https://arxiv.org/abs/1610.01213) (POPL 2017).

**Further features**

- [AU04] Thorsten Altenkirch and Tarmo Uustalu. [*Normalization by evaluation
  for λ→2*](https://doi.org/10.1007/978-3-540-24754-8_19) (FLOPS 2004) — NbE
  for simple types with booleans.
- [Fil01] Andrzej Filinski. [*Normalization by evaluation for the computational
  lambda-calculus*](https://doi.org/10.1007/3-540-45413-6_15) (TLCA 2001).
- [AS13] Danel Ahman and Sam Staton. [*Normalization by evaluation and
  algebraic effects*](https://doi.org/10.1016/j.entcs.2013.09.007) (MFPS 2013).
- [SPB23] Filip Sieczkowski, Mateusz Pyzik, and Dariusz Biernacki. [*A general
  fine-grained reduction theory for effect handlers*](https://doi.org/10.1145/3607848)
  (ICFP 2023) — includes the first NbE algorithm for effect handlers.
- [HJP23] Jason Z. S. Hu, Junyoung Jang, and Brigitte Pientka. [*Normalization
  by evaluation for modal dependent type theory*](https://doi.org/10.1017/S0956796823000060)
  (JFP 33, 2023).
- [SLK25] Matthew Sirman, Meven Lennon-Bertrand, and Neel Krishnaswami.
  [*Implementing a type theory with observational equality, using normalisation
  by evaluation*](https://doi.org/10.4230/LIPIcs.TYPES.2024.5) (TYPES 2024
  post-proceedings, 2025).

**Horizon features**

- [RS17] Emily Riehl and Michael Shulman. [*A type theory for synthetic
  ∞-categories*](https://arxiv.org/abs/1705.07442) (Higher Structures 1(1),
  2017) — extension types.
- [RKJ08] Patrick Rondon, Ming Kawaguchi, and Ranjit Jhala. [*Liquid
  types*](https://doi.org/10.1145/1375581.1375602) (PLDI 2008).
- [Vaz14] Niki Vazou, Eric Seidel, Ranjit Jhala, Dimitrios Vytiniotis, and
  Simon Peyton Jones. [*Refinement types for
  Haskell*](https://doi.org/10.1145/2628136.2628161) (ICFP 2014).
- [Swa16] Nikhil Swamy et al. [*Dependent types and multi-monadic effects in
  F\**](https://doi.org/10.1145/2837614.2837655) (POPL 2016) — F\*'s
  normaliser is itself NbE-based.
- [CCHM] Cyril Cohen, Thierry Coquand, Simon Huber, and Anders Mörtberg.
  [*Cubical type theory: a constructive interpretation of the univalence
  axiom*](https://arxiv.org/abs/1611.02108) (TYPES 2015).
- [Hub16] Simon Huber. *Cubical interpretations of type theory* (PhD thesis,
  2016).
- [SA21] Jonathan Sterling and Carlo Angiuli. [*Normalization for cubical type
  theory*](https://arxiv.org/abs/2101.11479) (LICS 2021).
- [VMA19] Andrea Vezzosi, Anders Mörtberg, and Andreas Abel. [*Cubical
  Agda*](https://doi.org/10.1145/3341691) (ICFP 2019).
- [cctt] András Kovács. [`cctt`](https://github.com/AndrasKovacs/cctt) — a
  performance-first Cartesian cubical type theory (HoTT 2023 talk): shallow
  explicit interval substitutions on values with force-on-demand,
  defunctionalised closures, canonicity-exploiting closed evaluation.
- [GSB19] Daniel Gratzer, Jonathan Sterling, and Lars Birkedal. [*Implementing
  a modal dependent type theory*](https://doi.org/10.1145/3341711) (ICFP 2019).
- [Gra22] Daniel Gratzer. [*Normalization for multimodal type
  theory*](https://doi.org/10.1145/3531130.3532398) (LICS 2022).
