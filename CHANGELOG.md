# Changelog

## Unreleased

- The generic core: the semantic domain `Value`, the `Eval` class, generic
  evaluation and readback, `nf` and `whnf`.
- Five demonstration languages, each with an `Eval` instance: lambda-pi,
  Booleans, lambda-let, pairs and naturals. All but Booleans also have a BNFC
  grammar, generated scope-safe syntax, a reference normaliser and a parser;
  the `split` of pairs and the `natrec` of naturals bind two names with one
  pattern.
- Elimination rules à la carte (`FreeFoil.NbE.Sum`): a fragment gives its
  rules once, for any language that contains it, and a `Sum` of fragments is
  a language with no code of its own. A language composed from fragments of
  functions, pairs and naturals demonstrates it, against the same language
  written in one signature, which is its baseline and its parser.
- `FreeFoil.NbE.Transform`: `foldAST` rebuilds a term bottom-up under an
  algebra that may return any term, with the binders mapped, and `hoistAST`
  changes the signature by a natural transformation. The languages share
  scope resolution and parsing in `Demo.Parsing`.
- Every language derives its `ZipMatchK` instance with free-foil's Template
  Haskell (`deriveZipMatchK`). The kind-generics default converted every node
  to its representation on comparison, which cost conversion checking and
  α-equivalence up to a third on a ten-constructor signature. free-foil is
  pinned at its `main` after [its #114](https://github.com/fizruk/free-foil/pull/114),
  whose written-out `ZipMatchK` instances
  for `Sum` and `Product` and traversal-free `nameBinderListOf` make the
  composed language's α-equivalence 2.7× faster and its conversion checking
  2.2× faster.
- A hand-written monomorphic NbE for lambda-pi as a performance baseline.
- A test suite and two benchmark suites, including a harness against the
  lambda-n-ways corpus.
- Performance work on the generic core; the current numbers are in
  `bench/lambda-n-ways/README.md`.
