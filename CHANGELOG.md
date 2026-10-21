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
- A hand-written monomorphic NbE for lambda-pi as a performance baseline.
- A test suite and two benchmark suites, including a harness against the
  lambda-n-ways corpus.
- Performance work on the generic core; the current numbers are in
  `bench/lambda-n-ways/README.md`.
