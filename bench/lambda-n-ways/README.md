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
    NBE.FreeFoil (generic): OK   1.31 ms ± 25 µs
    NBE.Foil:               OK   730  µs ± 53 µs
  random15
    NBE.FreeFoil (generic): OK   440  µs ± 30 µs
    NBE.Foil:               OK   94.7 µs ± 3.0 µs
  random20
    NBE.FreeFoil (generic): OK   438  µs ± 30 µs
    NBE.Foil:               OK   94.6 µs ± 6.7 µs
```

**Takeaway:** the generic free-foil normaliser is ~1.8× slower than the
hand-written foil NbE on the big factorial term (`nf`) and ~4.6× slower on the
random corpora. That is the price of the generic free-monad `AST` and name-based
scoping the fork's bespoke representation avoids — the two produce identical
normal forms.
