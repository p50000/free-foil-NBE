# Benchmarks

Microbenchmarks for lambda-pi normalisation. Each input is normalised three
ways: by the generic NbE (`nf`), by the hand-written monomorphic NbE
(`nf` from `LambdaPi.Monomorphic`, a baseline for the generic one) and by
the reference substitution normaliser (`nfSubst`). Thus they are directly comparable
on the same terms. Future implementation variants can be added as extra rows in
[`Main.hs`](Main.hs) without changing the inputs.

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
library where `nf`/`nfSubst` live is optimised, not just the benchmark driver.

## A sample run

Numbers below are from one run (Apple M3 Pro, macOS 15.7, GHC 9.10.3, `-O2`)
and are **not committed** — they are machine-specific, so treat them as a
relative reference, not an absolute target. Reproduce with
`cabal bench nbe-bench`.

- **Church `m^n`:** NbE wins by a widening margin as terms grow — at
  `2^10 = 1024`, `nf` ≈ 55 µs vs `nfSubst` ≈ 500 µs (**~9×**); the monomorphic `nf` ≈ 42 µs.
  Closures/sharing pay off on the exponential blow-up.
- **Church arithmetic (mult/add):** NbE ≈ 2× faster across the board.
- **Nested `let` (faithful):** the dramatic case — at depth 1000, `nf`
  ≈ 38 µs vs `nfSubst` ≈ 230 ms (**~6000×**). The reference re-copies the term on
  every binding (substitution blows up); NbE's environment/closures avoid it.
- **Nested identity redexes:** the one case NbE *loses* — ~1.4× slower than
  substitution on a long chain of trivial redexes (depth 1000: ≈ 15 µs vs
  ≈ 11 µs), since the closure machinery is overhead when there is nothing to
  share.
- **Nested `Pi` types:** the dependent-type worst case, and the regression
  guard for the exponential blow-up the eager-values representation fixed.
  `nf` scales *linearly* in nesting depth (100 / 500 / 1000 ≈ 14 / 71 /
  146 µs), and so does `nfSubst` (≈ 2.3 / 12 / 24 µs) — but here `nf` is a
  **constant factor slower, ~6×**, flat in the depth (down from ~24× before the
  performance series; the monomorphic `nf` sits at ~2.4×). `nfSubst` is a trivial single pass
  since these types hold no redexes, whereas NbE still builds and tears down
  closures. Recovering this factor with a shortcut for redex-free subterms is
  tracked in issue #3.

These contrasts motivate future optimisation variants (de Bruijn levels, glued
evaluation, memoised quoting, hash-consing).
