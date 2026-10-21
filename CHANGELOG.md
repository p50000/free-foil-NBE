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
- An elimination rule matches the value of its principal subterm through
  `eliminate`, which hands it a `Whnf`. `eval` returns an opaque `Value`, so
  a rule that matches a value directly does not type-check.
- Glued evaluation for definitions (`FreeFoil.NbE.Glue`): a defined name
  evaluates to a glued value, normal forms are read back folded, keeping the
  defined names, or unfolded, and conversion checking compares defined names
  folded first. Every language has glue. When no definition is used, it costs
  1–4% on β-heavy terms and nothing on the others.
- The composed language converts to and from the monolith with free-foil's
  `foldAST`. The languages share scope resolution and parsing in
  `Demo.Parsing`.
- free-foil is pinned at its `main` after
  [its #118](https://github.com/fizruk/free-foil/pull/118). `mkFreeFoil`
  generates the bifunctor, `ZipMatchK` and `NFData` instances of every
  generated signature, with `INLINE` pragmas, and the `NFData` instance of
  every generated pattern type. The generated modules carry no derive lines
  and no hand-written instances.
- The hand-written signatures, the fragments and Booleans, derive `ZipMatchK`
  with `deriveZipMatchK`, since the kind-generics default converts every node
  on comparison. With free-foil's written-out `ZipMatchK` instances for `Sum`
  and `Product` and its traversal-free `nameBinderListOf`, the composed
  language's α-equivalence is 2.7× faster and its conversion checking 2.2×
  faster.
- A hand-written monomorphic NbE for lambda-pi as a performance baseline.
- A test suite and two benchmark suites, including a harness against the
  lambda-n-ways corpus.
- Performance work on the generic core; the current numbers are in
  `bench/lambda-n-ways/README.md`.
