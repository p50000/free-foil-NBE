# Benchmarking against `lambda-n-ways`

This directory benchmarks free-foil-NBE's **real generic normaliser** against a
hand-written foil NbE, using the corpus of Weirich's
[`lambda-n-ways`](https://github.com/sweirich/lambda-n-ways) suite — specifically
Karina Tyulebaeva's foil fork,
[`KarinaTyulebaeva/lambda-n-ways`](https://github.com/KarinaTyulebaeva/lambda-n-ways).

Two implementations are compared on the fork's `nf` / `random15` / `random20`
groups:

- **`NBE.FreeFoil (generic)`** — `LambdaPi.nfNbe` from this repo's
  `lambda-pi-demo` library: the actual `Value` / `ScopedClosure` / `quote`
  machinery of [`FreeFoil.NbE`](../../src/FreeFoil/NbE.hs) running over the
  generic free-monad `AST`. The harness' `LC IdInt` is bridged to the scope-safe
  `AST` through the tested `LambdaPi.LambdaNWays` conversion — so this is the
  real code, not a copy that could drift.
- **`NBE.Foil`** — the fork's self-contained, hand-written foil NbE
  (`lib/Foil/NBE.hs`), which pays for no generic ("free") layer.

**The gap between the two columns is what we are measuring:** the cost of the
generic free-monad/`AST` layer. (The corpus is untyped — plain lambda calculus,
no `Pi` — so this exercises the *representation and generic machinery*, not the
dependent-type `Pi` fix. For the `Pi` numbers see the `nbe-bench` suite in
[`../`](../).)

## Running

Prerequisites: a modern GHC + cabal (tested: GHC 9.10.3, cabal 3.x).

```sh
# from the free-foil-NBE repo root:

# 1. clone the fork next to the harness (this path is gitignored).
#    --depth 1: the harness needs no history, and the fork carries a 166 MB
#    results/ directory, so a shallow clone (~216 MB) is much smaller than full.
git clone --depth 1 https://github.com/KarinaTyulebaeva/lambda-n-ways.git \
  bench/lambda-n-ways/lambda-n-ways-fork

# 2. build & run
cd bench/lambda-n-ways/nbe-harness
cabal run nbe-harness
```

The harness pulls the generic normaliser from this repo (`free-foil-nbe` +
`free-foil-nbe:lambda-pi-demo`, via its `cabal.project`) and the fork's
self-contained `Util.*` / `Foil.NBE` source plus the `lams/*.lam` corpus from the
clone. Nothing is copied into the fork and the fork's own build is not used.

Options: `--csv out.csv` to write results; `LAMS_DIR=/path/to/lams/` to point at
a corpus elsewhere (default `../lambda-n-ways-fork/lams/`).

### Why a modern GHC, and only part of the fork

The fork pins **GHC 8.10.7** (stack `lts-18.22`), which has **no native code
generator for Apple Silicon** (it needs LLVM `opt`/`llc` 9–12, which current
Homebrew no longer ships), and its many pinned legacy dependencies do not build
under a modern GHC either. So we do **not** build the whole fork: the harness
compiles only its *self-contained* `Util.*` and `Foil.NBE` modules (via
`hs-source-dirs`) together with this repo's packages, under one modern GHC. Both
columns use the same compiler and flags (`-O2`), so the difference between them
is meaningful.

## A sample run

Numbers from one run (Apple M3 Pro, macOS 14.4, GHC 9.10.3, `-O2`); machine-
specific, treat as relative. The first line is a correctness cross-check: the
generic normaliser's normal forms are alpha-equal to the baseline's on every
corpus term.

```
correctness: generic free-foil NbE vs fork baseline on 201 terms — ALL AGREE
All
  nf
    NBE.FreeFoil (generic): OK   1.78 ms,  8.4 MB allocated
    NBE.Foil:               OK   759  µs,  4.7 MB allocated
  random15
    NBE.FreeFoil (generic): OK   485  µs,  4.0 MB allocated
    NBE.Foil:               OK    95  µs,  924 KB allocated
  random20
    NBE.FreeFoil (generic): OK   456  µs,  3.9 MB allocated
    NBE.Foil:               OK    94  µs,  936 KB allocated
```

The two normalisers produce identical normal forms on all 201 terms. The generic
one costs about **4× the allocation** on the random corpora (≈1.8× on the big
factorial term), and time tracks allocation closely.

### Where the cost comes from

Profiling attributes the gap to the **representation, not the algorithm or the
scoping discipline**:

- **Not names-vs-levels, not the environment.** Both normalisers use the *same*
  name machinery — foil `Name`s and an `IntMap`-backed `Substitution` (the fork's
  `Foil.NBE` uses the identical `IntMap` substitution). So the gap is not de
  Bruijn indices/levels and not the environment structure.
- **Not dictionary dispatch.** Both are built at `-O2`, and the generic loop is
  specialized to the concrete signature (`INLINABLE` + `SPECIALIZE`), so the gap
  is not type-class overhead — specializing changed time by only ~5% and
  allocation not at all.
- **The generic free-monad representation.** `AST = Var | Node (sig …)` plus a
  two-level semantic domain (`Value` + per-scoped-subterm `ScopedClosure`) means
  every node is several heap objects — a `VNode` box, the `sig` cell, and a
  `ScopedClosure` — where the fork's monomorphic single-type GADT (`Expr` with an
  unpacked closure constructor) is one. That extra object *count* per node is the
  ~4×.

### How it could be reduced

- **Force the eval/quote recursion (applied).** Forcing the recursive
  constructions collapses intermediate thunks, cutting allocation ~13–30% (most
  on deep, sharing-heavy terms) with identical normal forms. It must stay lazy
  *under binders*: forcing a suspended `Pi` codomain eagerly regresses dependent
  types.
- **An eager `free-foil` AST (future).** Strict `AST`/`ScopedAST` fields would cut
  per-node thunk allocation further; to avoid the same `Pi` regression it must be
  *selectively* strict (strict spine, lazy scoped body), and belongs upstream as
  an opt-in.
- **A single-type value domain (future).** Collapsing `Value`/`ScopedClosure`
  into a decorated `AST` (as the fork's `Expr` does) removes one object layer, at
  some cost to the clean eval/quote split.

The residual gap is the intrinsic price of a *signature-generic* representation
over a hand-specialized monomorphic one that uses the same name machinery.
