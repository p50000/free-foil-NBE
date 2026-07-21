# Benchmarks

Microbenchmarks for lambda-pi normalisation. Each input is normalised two ways —
by NbE (`nfNbe`) and by the reference substitution normaliser (`nf`) — so the two
are directly comparable on the same terms. Future implementation variants can be
added as extra rows in [`Main.hs`](Main.hs) without changing the inputs.

## Running

```sh
cabal bench nbe-bench
```

To record a fresh baseline, or compare against the committed one:

```sh
# write a new baseline
cabal bench nbe-bench --benchmark-options '--csv bench/baseline.csv'

# compare a later run against it (fails on large regressions)
cabal bench nbe-bench --benchmark-options '--baseline bench/baseline.csv'
```

Uses [`tasty-bench`](https://hackage.haskell.org/package/tasty-bench); results
are forced with `sizeOf` (walking the whole normal form) rather than an
`NFData` instance, matching free-foil's own normalisation benchmark.

## Recorded baseline

[`baseline.txt`](baseline.txt) (human-readable) and [`baseline.csv`](baseline.csv)
(for `--baseline`). Numbers are machine-specific — treat them as a relative
reference on the machine that produced them, not an absolute target.

Headline from the recorded run (Apple Silicon, GHC 9.10.3, `-O2`):

- **Church `m^n`:** NbE wins by a widening margin as terms grow — at
  `2^10 = 1024`, `nfNbe` ≈ 74 µs vs `nf` ≈ 1.7 ms (~23×). Closures/sharing pay
  off on the exponential blow-up.
- **Church arithmetic (mult/add):** NbE ≈ 2× faster across the board.
- **Nested `let` (faithful):** the dramatic case — at depth 1000, `nfNbe`
  ≈ 48 µs vs `nf` ≈ 694 ms (**~14000×**). The reference re-copies the term on
  every binding (substitution blows up); NbE's environment/closures avoid it.
- **Nested identity redexes:** the one case NbE *loses* — ~2× slower than
  substitution on a long chain of trivial redexes (depth 1000: ≈ 18 µs vs
  ≈ 11 µs), since the closure machinery is overhead when there is nothing to
  share.

These contrasts motivate future optimisation variants (de Bruijn levels, glued
evaluation, memoised quoting, hash-consing).
