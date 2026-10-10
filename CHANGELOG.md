# Changelog

## Unreleased

- The generic core: the semantic domain `Value`, the `Eval` class, generic
  evaluation and readback, `nfNbe` and `whnfNbe`.
- Three demonstration languages: lambda-pi, Booleans and lambda-let, each
  with a BNFC grammar, generated scope-safe syntax, an `Eval` instance, a
  reference normaliser and a parser.
- A hand-written monomorphic NbE for lambda-pi as a performance baseline.
- A test suite and two benchmark suites, including a harness against the
  lambda-n-ways corpus.
- Performance work bringing the generic normaliser from 4.7× to 2.4× the
  time of a hand-written foil NbE on the lambda-n-ways random corpora, and
  from 2.4× to 1.3× on its factorial term; see `docs/design.md`.
