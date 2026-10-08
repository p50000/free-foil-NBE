# Benchmarking against `lambda-n-ways`

This directory benchmarks free-foil-NBE's **real generic normaliser** against
two hand-written foil NbEs, using the corpus of Weirich's
[`lambda-n-ways`](https://github.com/sweirich/lambda-n-ways) suite — specifically
Karina Tyulebaeva's foil fork,
[`KarinaTyulebaeva/lambda-n-ways`](https://github.com/KarinaTyulebaeva/lambda-n-ways).

Three implementations are compared on the fork's `nf` / `random15` / `random20`
groups:

- **`NBE.FreeFoil (generic)`** — `LambdaPi.nfNbe` from this repo's
  `lambda-pi-demo` library: the actual `Value` / `VSuspended` / `quote`
  machinery of [`FreeFoil.NbE`](../../src/FreeFoil/NbE.hs) running over the
  generic free-monad `AST`. The harness' `LC IdInt` is bridged to the scope-safe
  `AST` through the tested `LambdaPi.LambdaNWays` conversion — so this is the
  real code, not a copy that could drift.
- **`NBE.FreeFoil (monomorphic)`** — `LambdaPi.Monomorphic.nfMono`, a
  hand-written NbE with a monomorphic value type (one constructor per value
  form). It runs the same algorithm on the same scope-safe `AST`, with the
  same conversion, so it differs from the generic column only in the
  normaliser.
- **`NBE.Foil`** — the fork's self-contained, hand-written foil NbE
  (`lib/Foil/NBE.hs`), which pays for no generic ("free") layer. The pinned
  commit includes a strictness repair contributed from this investigation
  (KarinaTyulebaeva/lambda-n-ways#1: `eval` made strict in its environment;
  before it, the baseline allocated an `addSubst` thunk on every beta
  reduction). Note that numbers published before that fix compared against
  the pre-fix baseline, which was about 30% slower on these corpora.

**The gaps between the columns are what we measure.** Generic against
monomorphic is the cost of genericity in the normaliser, roughly what
generated monomorphic code could save. Monomorphic against the fork is the
cost of the generic `AST`, which both free-foil columns read, build and force.
(The corpus is untyped — plain lambda calculus,
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

# 4. or reproduce the table below: medians of 12 runs, one column per process,
#    column order rotated, allocations from the RTS (+RTS -T)
cabal build nbe-harness && ./medians.sh
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

## Results

Medians of 12 runs (`medians.sh`; Apple M3 Pro, GHC 9.10.3, `-O2`, free-foil
0.5.0); machine-specific, treat as relative. Each run measures one column in
a separate process, with the column order rotated, and first checks that both
free-foil columns agree with the baseline (up to alpha) on every corpus term.

| corpus | generic | monomorphic | `NBE.Foil` |
|---|---|---|---|
| nf (lennart) | 735 µs, 4.6 MB | 595 µs, 3.8 MB | 584 µs, 3.8 MB |
| random15 | 191 µs, 1.4 MB | 137 µs, 836 KB | 81 µs, 763 KB |
| random20 | 193 µs, 1.4 MB | 142 µs, 844 KB | 81 µs, 773 KB |

Against the baseline, the generic normaliser costs about **1.3× the time and
1.2× the allocation** on the factorial term, and **2.4× the time and 1.8× the
allocation** on the random corpora. At the start of the investigation these
were 2.4×/1.8× and 4.7×/4.3×, against the then-unrepaired baseline. Against
the monomorphic column, it costs 1.25× the time and 1.2× the allocation on the
factorial term, and 1.4× and 1.7× on the random corpora.

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

A generic node is a constructor box around a `sig` cell, so a stuck
application or a `Pi` value costs two heap objects where the monomorphic value
type pays one, and the generic readback refreshes binders through the
pattern-generic `withRefreshedPattern`. On the factorial term the monomorphic
column runs within 3% of the baseline; on the random corpora it closes about
half of the time gap.

The rest lies outside the normaliser. Both free-foil columns read and build
the generic `AST`, in which a lambda is at least four heap objects, and the
harness forces their results through free-foil's generic `NFData` instance.
Generated monomorphic code could remove the first part of the gap, but not
the second, as long as the normaliser works on free-foil's `AST`.
