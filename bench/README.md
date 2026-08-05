# Benchmarks

Microbenchmarks for lambda-pi normalisation. Each input is normalised two ways —
by NbE (`nfNbe`) and by the reference substitution normaliser (`nf`) — so the two
are directly comparable on the same terms. Future implementation variants can be
added as extra rows in [`Main.hs`](Main.hs) without changing the inputs.

## Running

```sh
cabal bench nbe-bench
```

Record your own baseline (the CSV path is gitignored, not committed) and compare
later runs against it:

```sh
# write a baseline
cabal bench nbe-bench --benchmark-options '--csv bench/baseline.csv'

# compare a later run against it (fails on large regressions)
cabal bench nbe-bench --benchmark-options '--baseline bench/baseline.csv'
```

Uses [`tasty-bench`](https://hackage.haskell.org/package/tasty-bench); results
are forced with `sizeOf` (walking the whole normal form) rather than an
`NFData` instance, matching free-foil's own normalisation benchmark. Every
component is built at `-O2` (`optimization: 2` in `cabal.project`), so the
library where `nfNbe`/`nf` live is optimised, not just the benchmark driver.

## A sample run

Numbers below are from one run (Apple M3 Pro, macOS 14.4, GHC 9.10.3, `-O2`) and
are **not committed** — they are machine-specific, so treat them as a relative
reference, not an absolute target. Reproduce with `cabal bench nbe-bench`.

- **Church `m^n`:** NbE wins by a widening margin as terms grow — at
  `2^10 = 1024`, `nfNbe` ≈ 64 µs vs `nf` ≈ 1.9 ms (**~30×**). Closures/sharing
  pay off on the exponential blow-up.
- **Church arithmetic (mult/add):** NbE ≈ 2–3× faster across the board.
- **Nested `let` (faithful):** the dramatic case — at depth 1000, `nfNbe`
  ≈ 51 µs vs `nf` ≈ 637 ms (**~13000×**). The reference re-copies the term on
  every binding (substitution blows up); NbE's environment/closures avoid it.
- **Nested identity redexes:** the one case NbE *loses* — ~1.7× slower than
  substitution on a long chain of trivial redexes (depth 1000: ≈ 17 µs vs
  ≈ 11 µs), since the closure machinery is overhead when there is nothing to
  share.
- **Nested `Pi` types:** the dependent-type worst case. `nfNbe` scales
  *linearly* in nesting depth (100 / 500 / 1000 ≈ 56 / 278 / 575 µs) — the
  regression guard for the exponential blow-up the eager-values representation
  fixed. (`nf` is a trivial single pass here since the types hold no redexes.)

These contrasts motivate future optimisation variants (de Bruijn levels, glued
evaluation, memoised quoting, hash-consing).
