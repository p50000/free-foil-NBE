# free-foil-NBE

A generic **normalisation-by-evaluation (NbE)** framework built on
[free-foil](https://github.com/fizruk/free-foil) (intrinsically-scoped abstract
syntax). You describe an object language as a signature and obtain NbE-based
normalisation with as little bespoke code as possible; normalisation is factored,
following Christiansen's tutorial, into an evaluator into semantic values and a
`quote` function back into syntax.

This realises the generic-`Closure` sketch (Figure 14) that the Free Foil paper
([Kudasov, Shakirova, Shalagin, Tyulebaeva, ICCQ 2024](https://arxiv.org/abs/2405.16384))
left as future work. The framework is demonstrated on a lambda-pi object
language.

**Current status.** The generic NbE core and a lambda-pi demonstration are in
place: a BNFC-generated parser/printer, free-foil Template Haskell for the
scope-safe syntax, a `tasty` test suite, and a `tasty-bench` benchmark suite (see
[bench/README.md](bench/README.md)). Next up is lifting the evaluator into a
reusable type class, so a new language is just a signature plus one instance.

The rest of this file is a practical guide to building, verifying, and running
everything. All commands are run from the repository root.

## Prerequisites

- **GHC 9.10.3 and cabal.** The compiler is pinned in `cabal.project`
  (`with-compiler: ghc-9.10.3`); install it via `ghcup` if needed.
- **Nothing else for normal use.** The BNFC-generated parser/printer are
  committed under `gen/`, so building, testing, and benchmarking need no extra
  tools.
- **Only to regenerate the grammar:** `bnfc`, `alex`, `happy`
  (`cabal install BNFC alex happy`, then ensure `~/.cabal/bin` is on `PATH`).

## What is where

| Path | What it is |
|------|-----------|
| `src/FreeFoil/NbE.hs` | The generic NbE core: the `Closure` value type and generic `quote'` (language-agnostic). |
| `demo/grammar/Syntax.cf` | The lambda-pi grammar (LBNF). |
| `gen/LambdaPi/Syntax/*` | BNFC/alex/happy output (lexer, parser, printer) — committed. |
| `demo/LambdaPi/Raw.hs`, `Generated.hs` | free-foil TH: config + generated scope-safe types, patterns, conversions, `Show`, `NFData`. |
| `demo/LambdaPi.hs` | The lambda-pi surface: `eval`, reference `nf`/`whnf`, NbE `nfNbe`. |
| `demo/LambdaPi/Parser.hs`, `PrettyPrint.hs` | `IsString` parsing; value printers (`ppValue`, `ppValueStruct`). |
| `demo/LambdaPi/LambdaNWays.hs` | Adapter to Weirich's `lambda-n-ways` harness (untyped `LC` bridge). |
| `test/` | `tasty` test suite. |
| `bench/` | `tasty-bench` microbenchmarks + recorded baseline. |

## Build

```sh
cabal build all
```

This builds the `free-foil-nbe` library, the internal `lambda-pi-syntax`
(generated parser) library, the `lambda-pi-demo` library, the `lambda-pi` test
suite, and the `nbe-bench` benchmark. It is warning-clean under `-Wall`.

## Run the tests

```sh
cabal test
# or, to see every test case:
cabal test --test-show-details=direct
```

Expected: **`All 40 tests passed`**. The suite covers:

- **beta-reduction** on closed terms;
- **normalisation under binders**;
- **`Pi`** (dependent function types): codomain redex, neutral codomain,
  non-dependent arrow;
- **neutrals with free variables**;
- **`parse . show` round-trips**;
- **value inspection** (`ppValue` / `ppValueStruct` / `Show`);
- the **lambda-n-ways adapter** (round-trip + `nbeNf`-vs-`refNf` agreement);
- **properties**: `nfNbe == nf` up to alpha-equivalence (free-foil's
  `alphaEquiv`) on random closed and open terms.

Useful flags:

```sh
cabal test --test-options='-p "Pi"'                      # run one group
cabal test --test-options='--quickcheck-tests 2000'      # more property cases
```

## Run the benchmarks

```sh
cabal bench nbe-bench
```

Each input is normalised two ways — by NbE (`nfNbe`) and by the reference
substitution normaliser (`nf`) — so they are directly comparable. Groups: Church
`m^n`, Church arithmetic (mult/add), a faithful nested-`let` chain, and nested
identity redexes.

Record or compare a baseline:

```sh
# write a baseline
cabal bench nbe-bench --benchmark-options '--csv bench/baseline.csv'
# compare a later run against the committed one
cabal bench nbe-bench --benchmark-options '--baseline bench/baseline.csv'
```

See [bench/README.md](bench/README.md) for the recorded baseline and its
interpretation (headline: NbE beats substitution ~23× on `2^10` and ~14000× on
nested `let`, but ~2× slower on the linear redex chain).

## Run NbE examples by hand (REPL)

Start a REPL on the demo library and set up the imports:

```sh
cabal repl lambda-pi-demo
```
```haskell
:set -XOverloadedStrings -XDataKinds
import LambdaPi                                  -- eval, nf, whnf, nfNbe, Show (terms)
import LambdaPi.Parser ()                        -- IsString: write terms as string literals
import LambdaPi.PrettyPrint (ppValue, ppValueStruct)
import FreeFoil.NbE (emptyScope, identitySubst)
```

**Normalise via NbE** (`nfNbe`), and cross-check against the reference `nf`.
Terms are written as string literals; `show` prints via the BNFC pretty-printer
(variables named by identifier — not alpha-canonical, but it re-parses):

```haskell
ghci> nfNbe emptyScope ("(\\x. x) (\\y. y)" :: LambdaPi VoidS)
\ x0 . x0
ghci> nf emptyScope ("(\\x. x) (\\y. y)" :: LambdaPi VoidS)        -- reference normaliser
\ x0 . x0
ghci> nfNbe emptyScope appTwo                                      -- Church 2·2 = 4
\ x1 . \ x2 . x1 (x1 (x1 (x1 x2)))
ghci> nfNbe emptyScope ("(a : \\t. t) -> (\\y. y) a" :: LambdaPi VoidS)   -- Pi: codomain redex reduced
(x0 : \ x0 . x0) -> x0
```

(`\\` in a Haskell string is a single backslash `\`, the lambda. You can also
build terms directly with the `Var`/`App`/`Lam`/`Pi` pattern synonyms and the
foil combinators — see `two`/`appTwo`/`neutralNbeOk` in `demo/LambdaPi.hs`.)

**Inspect a semantic value.** `eval` produces a `Closure`; two views:

```haskell
-- 'ppValue' — the value's MEANING: quote it back to a term and print.
ghci> ppValue emptyScope (eval emptyScope identitySubst ("\\x. x" :: LambdaPi VoidS))
\ x0 . x0

-- 'ppValueStruct' / 'show' — the value's STRUCTURE: #n neutral, {node |env=[..]} closure.
ghci> ppValueStruct (eval emptyScope identitySubst ("\\f. f" :: LambdaPi VoidS))
{lam x0. x0}
```

In `ppValueStruct`: `#n` is a neutral variable; `{lam …}` / `{app …}` / `{pi …}`
is a suspended node; scoped subterms print as their raw suspended AST; a
non-empty captured environment shows as ` |env=[…]` (the captured name ids).

**Compare NbE against the reference normaliser via the lambda-n-ways bridge**
(untyped `LC` terms with integer identifiers):

```haskell
ghci> import qualified LambdaPi.LambdaNWays as LNW
ghci> let idId = LNW.App (LNW.Lam (LNW.IdInt 0) (LNW.Var (LNW.IdInt 0))) (LNW.Lam (LNW.IdInt 1) (LNW.Var (LNW.IdInt 1)))
ghci> LNW.nbeNf idId                     -- normalise via NbE
Lam (IdInt 0) (Var (IdInt 0))
ghci> LNW.aeq (LNW.nbeNf idId) (LNW.refNf idId)   -- agrees with reference nf
True
```

## Regenerate the grammar (only if `Syntax.cf` changes)

```sh
cabal install BNFC alex happy      # once, if not already installed
./grammar-regen.sh                 # regenerates gen/LambdaPi/Syntax/{Abs,Lex,Par,Print}.hs
cabal build all && cabal test
```

The script runs `bnfc`, `alex`, and `happy` with relative paths so the output is
reproducible (no absolute paths leak into the generated files). Commit the
regenerated `gen/` files.

## One-shot check

```sh
cabal build all && cabal test && cabal bench nbe-bench
```

If this is green, everything is working.
