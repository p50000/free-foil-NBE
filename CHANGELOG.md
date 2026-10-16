# Changelog

## Unreleased

- The generic core: the semantic domain `Value`, the `Eval` class, generic
  evaluation and readback, `nf` and `whnf`.
- Four demonstration languages, each with an `Eval` instance: lambda-pi,
  Booleans, lambda-let and pairs. All but Booleans also have a BNFC grammar,
  generated scope-safe syntax, a reference normaliser and a parser; the
  `split` of pairs binds two names with one pattern.
- A hand-written monomorphic NbE for lambda-pi as a performance baseline.
- A test suite and two benchmark suites, including a harness against the
  lambda-n-ways corpus.
- Performance work on the generic core; the current numbers are in
  `bench/lambda-n-ways/README.md`.
