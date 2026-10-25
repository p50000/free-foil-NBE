# free-foil-NBE

Normalisation by evaluation (NbE), generic in the signature of the object
language, on top of [free-foil](https://github.com/fizruk/free-foil). A
language is a signature bifunctor and a binder type; it supplies its
elimination rules as one instance of a class with one method, and inherits
the semantic domain, evaluation, readback and the normalisers `nf` and
`whnf`. The normaliser is untyped and intensional: it decides β and the
language's own reductions, not η.

This realises the generic closure that the Free Foil paper (Kudasov,
Shakirova, Shalagin, Tyulebaeva, [ICCQ 2024](https://arxiv.org/abs/2405.16384))
left as future work.

**Status.** The core is in place and is demonstrated on five languages:
lambda-pi (functions and the dependent function type), Booleans (`if`, no
binders), lambda-let (`let`), pairs (projections, and `split` with a
pattern that binds two names) and naturals (primitive recursion, whose
`suc` branch binds two names), and on a language composed from fragments
of functions, pairs and naturals, whose rules the library combines
(`FreeFoil.NbE.Sum`); the same language written in one signature serves as
its baseline and lends it a parser. A hand-written monomorphic NbE is the
baseline of the generic normaliser, which runs within 1.25× of it on the
lambda-n-ways factorial term and 1.4× on its random corpora. The interface
is documented in the haddocks of `FreeFoil.NbE`.

## Limitations

- Readback consults no types: normal forms are β-normal, with the language's
  own reductions, and not η-normal.
- Values are built over the same signature as terms, so a language cannot
  have value formers that its syntax lacks, as extensional booleans and sums
  need.
- Conversion checking (`FreeFoil.NbE.Conversion`) compares values without
  reading them back and decides one-step η for the introduction forms a
  language marks with `etaMatchWith`, lambdas and pairs in the demos;
  readback does not.
- Top-level definitions (`FreeFoil.NbE.Definitions`) are non-recursive and
  always unfolded: no readback keeps the defined names.
- The core works with any free-foil pattern. The demo languages bind one
  variable at a time, except `split` in pairs and the `suc` branch of
  `natrec` in naturals, which bind two; the composed language has both
  shapes in one pattern type. No demo has nested or variable-length
  patterns.
- The languages are untyped, so normalisation need not terminate.
- Readback does not α-normalise: variables are named by their foil
  identifiers, so α-equivalent normal forms may print differently.

## Build, test, benchmark

GHC 9.10.3 and cabal; the compiler is pinned in `cabal.project`. The
BNFC-generated parsers are committed, so nothing else is needed.

```sh
cabal build all
cabal test            # 222 tests; --test-show-details=direct lists them
cabal bench nbe-bench
```

The lambda-n-ways comparison has its own guide in
[bench/lambda-n-ways/README.md](bench/lambda-n-ways/README.md); the
microbenchmarks are described in [bench/README.md](bench/README.md). To
change a grammar, install `bnfc`, `alex` and `happy`, run
`./grammar-regen.sh`, and commit the regenerated files under `gen/`.

## What is where

| Path | What it is |
|------|-----------|
| `src/FreeFoil/NbE.hs` | The core: `Value`, the `Eval` class, generic `eval` and `quote`, `nf` and `whnf`. |
| `src/FreeFoil/NbE/Conversion.hs` | Conversion checking on values: `conv`, `convertible` and `convertibleUnder`. |
| `src/FreeFoil/NbE/Definitions.hs` | Top-level definitions: a telescope and the environment it gives to `eval`. |
| `src/FreeFoil/NbE/Sum.hs` | Elimination rules à la carte: `EvalF` for a fragment, the `Eval` instance of a `Sum` of fragments. |
| `demo/grammar/<Lang>/Syntax.cf`, `gen/<Lang>/` | The LBNF grammar of each demo language and the committed BNFC output. |
| `demo/<Lang>/Raw.hs`, `Generated.hs` | free-foil's Template Haskell: the configuration and the generated scope-safe syntax. |
| `demo/LambdaPi.hs`, `demo/LambdaLet.hs`, `demo/Booleans.hs`, `demo/Pairs.hs`, `demo/Naturals.hs` | The languages: pattern synonyms, the `Eval` instance, a reference normaliser. |
| `demo/<Lang>/Examples.hs` | Example terms of each language, each with its normal form. |
| `demo/Fragments/*.hs` | The fragments of functions, pairs and naturals, their shared pattern type, and the language composed from them. |
| `demo/LambdaPi/Parser.hs`, `PrettyPrint.hs` | Terms as string literals; two printers for values. |
| `baselines/LambdaPi/Monomorphic.hs` | The monomorphic baseline, `LambdaPi.Monomorphic.nf`. |
| `baselines/LambdaPi/LambdaNWays.hs` | The bridge to the lambda-n-ways harness. |
| `baselines/Monolith.hs`, `baselines/Monolith/` | The monolithic language, functions, pairs and naturals in one signature: the baseline of the composed language, with its parser. |
| `parsing/Demo/Parsing.hs` | Parsing shared by the languages: a BNFC parser, then scope resolution in a scope with named free variables. |
| `test/`, `bench/` | The test suite; the microbenchmarks and the lambda-n-ways harness. |

## A first look

```sh
cabal repl lambda-pi-demo
```
```haskell
ghci> :set -XOverloadedStrings -XDataKinds
ghci> import LambdaPi
ghci> import LambdaPi.Parser ()
ghci> import Control.Monad.Foil (emptyScope)
ghci> nf emptyScope ("(\\x. x) (\\y. y)" :: LambdaPi VoidS)
\ x0 . x0
ghci> whnf emptyScope ("\\f. (\\x. x) f" :: LambdaPi VoidS)   -- stops at the binder
\ x0 . (\ x1 . x1) x0
ghci> nf emptyScope ("(a : \\t. t) -> (\\y. y) a" :: LambdaPi VoidS)
(x0 : \ x0 . x0) -> x0
```

`LambdaPi.PrettyPrint` shows a value either by quoting it back (`ppValue`)
or structurally, with its suspended bodies and their environments
(`ppValueStruct`, also `show`). Each language has ready-made terms with
their normal forms in its `Examples` module; lambda-let works the same way
from `cabal repl lambda-let-demo`.

## References

- D. T. Christiansen. *Checking dependent types with normalization by
  evaluation: a tutorial.* [davidchristiansen.dk/tutorials/nbe](https://davidchristiansen.dk/tutorials/nbe/).
  The evaluate-then-quote structure.
- A. Kovács. [elaboration-zoo](https://github.com/AndrasKovacs/elaboration-zoo)
  and [smalltt](https://github.com/AndrasKovacs/smalltt). The eager-values
  domain with one suspension point per binder.
- A. Abel. *Normalization by evaluation: dependent types and impredicativity.*
  Habilitation, 2013. Type-directed readback and the neutral-versus-value
  split, which this library leaves for later.
- U. Berger and H. Schwichtenberg. *An inverse of the evaluation functional
  for typed λ-calculus.* LICS 1991. The origin of NbE.
- N. Kudasov, R. Shakirova, E. Shalagin, K. Tyulebaeva. *Free Foil:
  generating efficient and scope-safe abstract syntax.* ICCQ 2024.
  [arXiv:2405.16384](https://arxiv.org/abs/2405.16384). The syntax, and the
  sketch this library realises.
