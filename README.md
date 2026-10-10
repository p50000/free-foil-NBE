# free-foil-NBE

Normalisation by evaluation (NbE), generic in the signature of the object
language, on top of [free-foil](https://github.com/fizruk/free-foil). A
language is a signature bifunctor and a binder type; it supplies its
elimination rules as one instance of a class with one method, and inherits
the semantic domain, evaluation, readback and the normalisers `nfNbe` and
`whnfNbe`. The normaliser is untyped and intensional: it decides β and the
language's own reductions, not η.

This realises the generic closure that the Free Foil paper (Kudasov,
Shakirova, Shalagin, Tyulebaeva, [ICCQ 2024](https://arxiv.org/abs/2405.16384))
left as future work.

**Status.** The core is in place and is demonstrated on three languages:
lambda-pi (functions and the dependent function type), Booleans (`if`, no
binders) and lambda-let (`let`). A hand-written monomorphic NbE serves as a
baseline; the generic normaliser runs within 1.25× of it on the
lambda-n-ways factorial term and 1.4× on its random corpora. What is
implemented, the decisions behind the design, and what is planned are in
[docs/design.md](docs/design.md).

## Build, test, benchmark

GHC 9.10.3 and cabal; the compiler is pinned in `cabal.project`. The
BNFC-generated parsers are committed, so nothing else is needed.

```sh
cabal build all
cabal test            # 79 tests; --test-show-details=direct lists them
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
| `src/FreeFoil/NbE.hs` | The core: `Value`, the `Eval` class, generic `eval` and `quote`, `nfNbe` and `whnfNbe`. |
| `demo/grammar/<Lang>/Syntax.cf`, `gen/<Lang>/` | The LBNF grammar of each demo language and the committed BNFC output. |
| `demo/<Lang>/Raw.hs`, `Generated.hs` | free-foil's Template Haskell: the configuration and the generated scope-safe syntax. |
| `demo/LambdaPi.hs`, `demo/LambdaLet.hs`, `demo/Booleans.hs` | The languages: pattern synonyms, the `Eval` instance, a reference normaliser. |
| `demo/LambdaPi/Parser.hs`, `PrettyPrint.hs` | Terms as string literals; two printers for values. |
| `demo/LambdaPi/Monomorphic.hs` | The monomorphic baseline, `nfMono`. |
| `demo/LambdaPi/LambdaNWays.hs` | The bridge to the lambda-n-ways harness. |
| `test/`, `bench/` | The test suite; the microbenchmarks and the lambda-n-ways harness. |
| `docs/design.md` | What it is, the interface, assumptions, decisions, plans. |

## A first look

```sh
cabal repl lambda-pi-demo
```
```haskell
ghci> :set -XOverloadedStrings -XDataKinds
ghci> import LambdaPi
ghci> import LambdaPi.Parser ()
ghci> import Control.Monad.Foil (emptyScope)
ghci> nfNbe emptyScope ("(\\x. x) (\\y. y)" :: LambdaPi VoidS)
\ x0 . x0
ghci> whnfNbe emptyScope ("\\f. (\\x. x) f" :: LambdaPi VoidS)   -- stops at the binder
\ x0 . (\ x1 . x1) x0
ghci> nfNbe emptyScope ("(a : \\t. t) -> (\\y. y) a" :: LambdaPi VoidS)
(x0 : \ x0 . x0) -> x0
```

`LambdaPi.PrettyPrint` shows a value either by quoting it back (`ppValue`)
or structurally, with its suspended bodies and their environments
(`ppValueStruct`, also `show`). Lambda-let works the same way from
`cabal repl lambda-let-demo`, with ready-made terms in `LambdaLet.Examples`.

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
