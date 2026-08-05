# Benchmarking against `lambda-n-ways`

This directory lets you benchmark the free-foil-NBE normaliser against the
implementations in Weirich's [`lambda-n-ways`](https://github.com/sweirich/lambda-n-ways)
suite — specifically Karina Tyulebaeva's foil fork,
[`KarinaTyulebaeva/lambda-n-ways`](https://github.com/KarinaTyulebaeva/lambda-n-ways),
whose foil-based NbE implementations live under `lib/`.

The harness is **untyped** (plain lambda calculus, no `Pi`), so it does *not*
exercise the dependent-type path — it measures our semantic-value representation
(`Value` / `ScopedClosure`, the eager-values NbE) against the field on the
standard workload. For the dependent-type numbers that motivated that
representation, see the `nbe-bench` suite in [`../`](../).

Contents:

| File | What it is |
|------|-----------|
| `EagerNBE.hs` | The port: our eager-values NbE as a `lambda-n-ways` `LambdaImpl` (`impl_name = "NBE.FreeFoilEager"`), specialised to untyped LC and reusing the fork's foil primitives from `Foil.NBE`. Drop it into the fork's `lib/Foil/`. |
| `nbe-harness/` | A minimal `tasty-bench` project that runs the fork's `nf` / `random15` / `random20` groups for our port + the fork's `Foil.NBE` baseline, using a **modern GHC**. |

---

## Why two ways to run it

The fork pins **GHC 8.10.7** (stack `lts-18.22`). That compiler has **no native
code generator for Apple Silicon (aarch64-darwin)** — it requires LLVM `opt`/`llc`
in the range 9–12, which current Homebrew no longer ships. So:

- **On Linux / Intel macOS** (or anywhere GHC 8.10.7 builds): use **Path A** and
  run the fork's own benchmark unmodified.
- **On Apple Silicon** (or if you just want a quick, focused run): use **Path B**,
  the minimal harness, which reuses the fork's *real* source and corpus but
  compiles with any modern GHC (≥ 9.2 has native aarch64 codegen; tested on
  9.10.3).

Both paths produce the same measurement — normalise the corpus, force the result.

---

## Path B — minimal harness (recommended; works on Apple Silicon)

Prerequisites: a modern GHC + cabal (tested: GHC 9.10.3, cabal 3.x). No stack, no
LLVM, no GHC 8.10.7.

```sh
# from the free-foil-NBE repo root; adjust FORK to taste
git clone https://github.com/KarinaTyulebaeva/lambda-n-ways.git /tmp/lambda-n-ways
FORK=/tmp/lambda-n-ways

# 1. drop the port module into the fork
cp bench/lambda-n-ways/EagerNBE.hs "$FORK/lib/Foil/EagerNBE.hs"

# 2. drop the harness inside the fork (so its ../lib and ../lams paths resolve)
cp -R bench/lambda-n-ways/nbe-harness "$FORK/nbe-harness"

# 3. build & run
cd "$FORK/nbe-harness"
cabal run nbe-harness
```

That's the whole setup for Path B — no edits to the fork's own `.cabal` or
`Suite.hs` are needed, because the harness lists `Foil.EagerNBE` in its own
`other-modules` and references it directly.

Expected output (numbers are machine-dependent):

```
correctness: eager-values port vs baseline on 201 terms — ALL AGREE
All
  nf
    NBE.FreeFoilEager: OK
      827  μs ±  57 μs
    NBE.Foil:          OK
      716  μs ±  27 μs
  random15
    NBE.FreeFoilEager: OK   97.0 μs ± 8.0 μs
    NBE.Foil:          OK   94.9 μs ± 7.9 μs
  random20
    NBE.FreeFoilEager: OK   97.5 μs ± 9.7 μs
    NBE.Foil:          OK   93.8 μs ± 6.8 μs
```

The first line is a correctness cross-check: the port's normal forms are
alpha-equal to the baseline's on every corpus term. To write a CSV, pass
`--csv out.csv`; to point at a corpus elsewhere, set `LAMS_DIR` (default
`../lams/`).

## Path A — inside the fork's own benchmark (Linux / Intel)

Use this to compare against *all* the fork's implementations with its native
criterion benchmark.

1. Copy the port in: `cp bench/lambda-n-ways/EagerNBE.hs "$FORK/lib/Foil/EagerNBE.hs"`.
2. Register the module in `$FORK/lambda-n-ways.cabal` — add to the library's
   `exposed-modules`, next to `Foil.NBE`:
   ```
         Foil.NBE
         Foil.EagerNBE
   ```
3. Register the impl in `$FORK/lib/Suite.hs`:
   ```haskell
   import qualified Foil.EagerNBE            -- near the other Foil imports

   -- add Foil.EagerNBE.impl to the impls list you benchmark, e.g. inside
   -- `freeScoped` (or `all_impls`):
       Foil.EagerNBE.impl,
   ```
4. Build and run the normalisation groups:
   ```sh
   cd "$FORK"
   make normalize          # or: stack run -- --match prefix "nf/"
   ```
   Our row appears as `nf/NBE.FreeFoilEager`, `random15/NBE.FreeFoilEager`, etc.

Note: on Apple Silicon this fails at `stack build` with
`ghc: could not execute: opt` (the missing LLVM described above) — use Path B
instead.

---

## What the port is

`EagerNBE.hs` mirrors the representation shipped in
[`src/FreeFoil/NbE.hs`](../../src/FreeFoil/NbE.hs): a semantic `Value` whose term
subterms are already values (`VVar` / `VApp`) and whose lambda body is a
`ScopedClosure` capturing its environment. `eval` suspends bodies and reduces
applications; `quote` reads a value back, visiting each subterm exactly once. In
the untyped fragment there is no `Pi`, so it coincides behaviourally with the
fork's closure NbE (`Foil.NBE`); the point is to exercise *our* representation on
the shared corpus. Measured result: on par with the hand-written baseline
(within ~10–15 % on `nf`, within noise on the random corpora), with identical
normal forms.
