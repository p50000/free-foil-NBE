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
  (`lib/Foil/NBE.hs`), which pays for no generic ("free") layer. The pinned
  commit includes a strictness repair contributed from this investigation
  (KarinaTyulebaeva/lambda-n-ways#1: `eval` made strict in its environment;
  before it, the baseline allocated an `addSubst` thunk on every beta
  reduction). Note that numbers published before that fix compared against
  the pre-fix baseline, which was about 30% slower on these corpora.

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

# 2. pin the baseline, so the numbers are a fixed reference (this is the
#    merge of the strict-eval repair, KarinaTyulebaeva/lambda-n-ways#1)
git -C bench/lambda-n-ways/lambda-n-ways-fork \
  fetch --depth 1 origin 1f507f589ec12366757fdc3ee1fa499855615df3
git -C bench/lambda-n-ways/lambda-n-ways-fork \
  checkout 1f507f589ec12366757fdc3ee1fa499855615df3

# 3. build & run
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

Numbers from one run (Apple M-series, GHC 9.10.3, `-O2`, free-foil pinned to
the HEAD carrying fizruk/free-foil#86, #87 and #88); machine-specific, treat
as relative. The first line is a correctness cross-check: the generic
normaliser's normal forms are alpha-equal to the baseline's on every corpus
term.

```
correctness: generic free-foil NbE vs fork baseline on 201 terms — ALL AGREE
All
  nf
    NBE.FreeFoil (generic): OK   619  µs,  4.4 MB allocated
    NBE.Foil:               OK   459  µs,  3.6 MB allocated
  random15
    NBE.FreeFoil (generic): OK   166  µs,  1.3 MB allocated
    NBE.Foil:               OK    65  µs,  745 KB allocated
  random20
    NBE.FreeFoil (generic): OK   166  µs,  1.3 MB allocated
    NBE.Foil:               OK    67  µs,  755 KB allocated
```

The generic normaliser costs about **1.2× the allocation and 1.3× the time**
on the big factorial term, and **1.75× the allocation and 2.5× the time** on
the random corpora. At the start of the investigation the comparison stood
at 1.8×/2.4× and 4.3×/4.7× respectively — against the then-unrepaired
baseline, so the true starting gap was wider still.

### Where the cost went

The gap was closed by a sequence of measured changes:

- **Concrete `CoSinkable` instances** (fizruk/free-foil#87). The empty-instance
  idiom left every binder operation on a GenericK representation traversal;
  `mkFreeFoil` now generates the delegating instance. This alone was −40% time
  and −45% allocation on the random corpora.
- **Raw-node `evalSig`.** The `Eval` class hands the eliminator the raw syntax
  node and the environment, so a redex no longer pays for an interpreted node
  it immediately discards: −28% time and −29% allocation on lennart.
- **Full specialisation.** The `nfNbe` pragma alone left the recursive
  `eval`/`evalSig` calls dictionary-dispatched; explicit `SPECIALIZE` pragmas
  for `eval`/`quote`/`quoteScopedClosure` gave another −12…−18% time.
- **Scoped pattern traversals** (fizruk/free-foil#88). `withPattern` and the
  refreshers hand back the extended scope, removing the second traversal per
  binder in the readback: −11% allocation, −7% time on the random corpora.
- **Suspended nodes.** A node with binders is suspended as a whole
  (`VSuspended`), fusing the node box with the closure; a lambda value is two
  heap objects instead of three. This closed most of the remaining gap on the
  factorial term.

### What remains

The remaining gap is the two-level representation itself. A generic node is
a constructor box around a `sig` cell, so a value costs two heap objects
where the fork's monomorphic GADT (`Expr` with an unpacked closure
constructor) pays one. Merging the two objects requires monomorphic code,
generated or hand-written, and is out of scope here; environment `IntMap`
costs are shared with the baseline.

The residual gap is the intrinsic price of a *signature-generic* representation
over a hand-specialized monomorphic one that uses the same name machinery.
