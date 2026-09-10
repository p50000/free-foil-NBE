# free-foil-NBE

A generic **normalisation-by-evaluation (NbE)** framework built on
[free-foil](https://github.com/fizruk/free-foil) (intrinsically-scoped abstract
syntax). You describe an object language as a signature and obtain NbE-based
normalisation with as little bespoke code as possible; normalisation is factored,
following [Christiansen's tutorial](https://davidchristiansen.dk/tutorials/nbe/),
into an evaluator into semantic values and a `quote` function back into syntax.

This realises the generic-`Closure` sketch (Figure 14) that the Free Foil paper
([Kudasov, Shakirova, Shalagin, Tyulebaeva, ICCQ 2024](https://arxiv.org/abs/2405.16384))
left as future work. The framework is demonstrated on a series of small object
languages.

**Current status.** The generic NbE core is in place: an object language is a
signature plus one `Eval` instance (its elimination rules), and evaluation,
quoting, and `nfNbe`/`whnfNbe` are inherited. Three demo languages exercise
it — **lambda-pi** (functions and `Pi`, plus the benchmark harnesses),
**Booleans** (`if`, no binders), and **lambda-let** (`let`-bindings — the
first entry of a planned series of per-feature demo languages, each a BNFC
grammar, the free-foil TH wiring, one hand-written module, and a file of
examples). A `tasty` test suite and a `tasty-bench` benchmark suite cover
them (see [bench/README.md](bench/README.md)).

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
| `src/FreeFoil/NbE.hs` | The generic NbE core: the `Value` semantic domain (`VVar`/`VNode`/`VSuspended`), the `Eval` class (a language supplies only its elimination rules), and the generic `eval`/`quote`/`nfNbe`/`whnfNbe` (language-agnostic). |
| `demo/grammar/<Lang>/Syntax.cf` | The LBNF grammars (one directory per demo language: `LambdaPi`, `LambdaLet`). |
| `gen/<Lang>/Syntax/*` | BNFC/alex/happy output (lexer, parser, printer) — committed. |
| `demo/LambdaPi/Raw.hs`, `Generated.hs` | free-foil TH: config + generated scope-safe types, patterns, conversions, `Show`, `NFData`. |
| `demo/LambdaPi.hs` | The lambda-pi surface: its one-rule `Eval` instance (beta), reference `nf`/`whnf`, and the inherited NbE `nfNbe`/`whnfNbe`. |
| `demo/Booleans.hs` | A second object language (Booleans with `if`) — one `Eval` instance, no binders — demonstrating the core is signature-generic, not lambda-pi-shaped. |
| `demo/LambdaLet.hs`, `demo/LambdaLet/*` | The lambda-let demo language (zoo series, step 1): untyped lambda plus `let` — an eliminator that always fires, so no `let` survives normalisation. Same four-part shape: grammar, `Raw.hs`/`Generated.hs` TH wiring, the hand-written surface with the `Eval` instance and reference normalisers, and `Examples.hs`. |
| `demo/LambdaPi/Parser.hs`, `PrettyPrint.hs` | `IsString` parsing; value printers (`ppValue`, `ppValueStruct`). |
| `demo/LambdaPi/LambdaNWays.hs` | Adapter to Weirich's `lambda-n-ways` harness (untyped `LC` bridge). |
| `test/` | `tasty` test suite. |
| `bench/` | `tasty-bench` microbenchmarks (NbE vs reference); `bench/lambda-n-ways/` is a guide + harness benchmarking the generic normaliser against Weirich's `lambda-n-ways` suite. |

## Build

```sh
cabal build all
```

This builds the `free-foil-nbe` library, the generated-parser libraries
(`lambda-pi-syntax`, `lambda-let-syntax`), the demo libraries
(`lambda-pi-demo`, `lambda-let-demo`), the `lambda-pi` test suite, and the
`nbe-bench` benchmark. It is warning-clean under `-Wall`.

## Run the tests

```sh
cabal test
# or, to see every test case:
cabal test --test-show-details=direct
```

Expected: **`All 62 tests passed`**. The suite covers:

- **beta-reduction** on closed terms;
- **normalisation under binders**;
- **`Pi`** (dependent function types): codomain redex, neutral codomain,
  non-dependent arrow, and a deep-nesting regression (normalisation stays
  linear in `Pi`-depth);
- **neutrals with free variables**;
- **`parse . show` round-trips**;
- **value inspection** (`ppValue` / `ppValueStruct` / `Show`);
- the **lambda-n-ways adapter** (round-trip + `nbeNf`-vs-`refNf` agreement);
- **lambda-let** (zoo step 1): `nfNbe` vs reference `nf` on every example,
  shadowing, `let` bound to a neutral, and the `whnfNbe`/`nfNbe` split on a
  `let` under a binder;
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
`m^n`, Church arithmetic (mult/add), a faithful nested-`let` chain, nested
identity redexes, and nested `Pi` types (the dependent-type worst case that
motivated the eager-values representation).

Record your own baseline (the CSV path is gitignored, not committed) and compare
later runs against it:

```sh
# write a baseline
cabal bench nbe-bench --benchmark-options '--csv bench/baseline.csv'
# compare a later run against it (fails on large regressions)
cabal bench nbe-bench --benchmark-options '--baseline bench/baseline.csv'
```

See [bench/README.md](bench/README.md) for a sample run and its interpretation
(headline: NbE beats substitution ~30× on `2^10` and ~13000× on nested `let`,
but ~1.7× slower on the linear redex chain).

## Run NbE examples by hand (REPL)

Start a REPL on the demo library and set up the imports:

```sh
cabal repl lambda-pi-demo
```
```haskell
:set -XOverloadedStrings -XDataKinds
import LambdaPi                                  -- eval, nf, whnf, nfNbe, whnfNbe, Show (terms)
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

**Weak-head normal form** (`whnfNbe`) shares `eval` with `nfNbe` and differs only
in how far quoting is driven: it reduces the head but stops at binders, so a redex
under a lambda survives (whereas `nfNbe` reduces it):

```haskell
ghci> whnfNbe emptyScope ("\\f. (\\x. x) f" :: LambdaPi VoidS)   -- redex under the binder kept
\ x0 . (\ x1 . x1) x0
ghci> nfNbe   emptyScope ("\\f. (\\x. x) f" :: LambdaPi VoidS)   -- fully normalised
\ x0 . x0
```

(`\\` in a Haskell string is a single backslash `\`, the lambda. You can also
build terms directly with the `Var`/`App`/`Lam`/`Pi` pattern synonyms and the
foil combinators — see `two`/`appTwo`/`neutralNbeOk` in `demo/LambdaPi.hs`.)

**Lambda-let** works the same way from its own library
(`cabal repl lambda-let-demo`); ready-made terms live in `LambdaLet.Examples`:

```haskell
ghci> import LambdaLet
ghci> import LambdaLet.Examples
ghci> import FreeFoil.NbE (emptyScope)
ghci> nfNbe emptyScope letChurch          -- let two = \s. \z. s (s z) in two two
\ x1 . \ x2 . x1 (x1 (x1 (x1 x2)))
ghci> whnfNbe emptyScope letUnderLam      -- a let under a lambda survives whnf…
\ x0 . let x1 = x0 in x1 x1
ghci> nfNbe emptyScope letUnderLam        -- …and is reduced by nf
\ x0 . x0 x0
```

**Inspect a semantic value.** `eval` produces a `Value`; two views:

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

## Regenerate the grammars (only if a `Syntax.cf` changes)

```sh
cabal install BNFC alex happy      # once, if not already installed
./grammar-regen.sh                 # regenerates gen/<Lang>/Syntax/{Abs,Lex,Par,Print}.hs
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

## References

The design rests on the following work, grouped by the decision each informs.

**Foundation — intrinsically-scoped abstract syntax.**

- N. Kudasov, R. Shakirova, E. Shalagin, K. Tyulebaeva. *Free Foil: Generating
  Efficient and Scope-Safe Abstract Syntax.* ICCQ 2024.
  [arXiv:2405.16384](https://arxiv.org/abs/2405.16384) — the scope-safe `AST` and
  the generic `Closure` sketch (Figure 14) this project realises.

**NbE, factored as `eval` then `quote`.**

- D. T. Christiansen. *Checking Dependent Types with Normalization by Evaluation:
  A Tutorial.* [davidchristiansen.dk/tutorials/nbe](https://davidchristiansen.dk/tutorials/nbe/)
  — the evaluate-into-values / quote-back-to-syntax structure the demo follows.
- U. Berger, H. Schwichtenberg. *An Inverse of the Evaluation Functional for
  Typed λ-calculus.* LICS 1991.
  [pdf](https://www.mathematik.uni-muenchen.de/~schwicht/papers/lics91/paper.pdf)
  — the origin of NbE (`normalize = reify ∘ eval`).

**The eager-values representation** (`Value` / `ScopedClosure`, and the fix that
made nested `Pi` linear).

- A. Kovács. *elaboration-zoo* and *smalltt.*
  [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo),
  [smalltt](https://github.com/AndrasKovacs/smalltt) — the implementation
  reference: a single suspension point (environment + body), a `Pi`'s domain
  evaluated eagerly and its codomain kept as a closure, and neutrals as a head
  with a spine. Directly grounds our representation.
- A. Abel. *Normalization by Evaluation: Dependent Types and Impredicativity.*
  Habilitation, LMU Munich, 2013.
  [pdf](https://www.cse.chalmers.se/~abela/habil.pdf) — NbE for dependent types:
  reflect/reify with type-directed readback and the neutral-versus-value split.

**Background for future phases (sums, type-directed readback).**

- O. Danvy. *Type-Directed Partial Evaluation.* POPL 1996.
  [doi:10.1145/237721.237784](https://doi.org/10.1145/237721.237784).
- S. Lindley. *Normalisation by Evaluation in the Compilation of Typed Functional
  Programming Languages.* PhD thesis, University of Edinburgh, 2005.
  [handle](https://era.ed.ac.uk/handle/1842/778) — NbE with coproducts/sums, the
  hard case deferred to a later phase.
