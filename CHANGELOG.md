# Changelog

## Unreleased

- Evaluation, readback and conversion take, beside the scope, a context the
  client supplies. A language's `Eval` instance states what it needs of the
  context, and the demonstration languages use `NoContext`, which knows
  nothing beyond the scope. Under a binder the language says what the
  context learns (`extendScopedWith`, in the style of `etaMatchWith`). By
  default a binder only adds its names, so any sinkable context works with
  any language.
- A language may refine a value by the context (`refineVar` for a
  variable, `refineSig` for a node), for example η-expand a neutral at the
  type in its annotation or in the context. Readback and conversion refine
  a value before they look at it, except at the heads of nodes
  (`HasHeads`), the positions an elimination rule eliminates. By default
  nothing is refined and no position is a head. `HasHeads` is a superclass
  of `Eval` and `EvalF`, so every language and fragment gives an instance,
  possibly empty. A fragment refines with `refineVarF` and `refineSigF`,
  and a sum takes the first summand that refines.
- A context may give the free names of a language values (`definition`,
  by default from `HasDefinitions`),
  which `eval` unfolds where the names are used. `NoContext` gives none.
  Top-level definitions (`FreeFoil.NbE.Definitions`) are such a context,
  built one definition at a time, and a term is normalised in it with
  plain `nf`.
- An elimination rule matches the value of its principal subterm through
  `eliminate`, which hands it a `Whnf` to match with `VVar`, `VNode`,
  `VSuspended` and `Stuck`. `eval` returns an opaque `Value`, built with
  `vvar`, `vnode`, `vsuspended` and `vglued`, so a rule that matches a
  value directly does not type-check; `force` looks through the glue of a
  value for inspection.
- Glued evaluation for definitions, after Kovács: a defined name evaluates
  to the name glued to the lazy value of its body. Readback follows the
  side the context says (`unfolding`, by default from `HasDefinitions`), so
  that top-level definitions read back unfolded or folded (`Unfolding`).
  Conversion compares glued values folded first.
- Evaluation of annotated terms (`FreeFoil.NbE.Annotated`): a language
  whose rules are fragments evaluates terms over free-foil's `AnnSig`,
  ignoring the annotations. Values carry the annotation's blank.
- Conversion checking decides η for lambdas and pairs by shape,
  through a language's `etaMatchWith`, after Coquand (1996) and Abel and
  Coquand (2007).
- The generic core: the semantic domain `Value`, the `Eval` class, generic
  evaluation and readback, `nf` and `whnf`.
- A demonstration language whose context holds types, `DependentTypes`,
  with functions and pairs over a universe and a unit type. Functions and
  pairs have η by shape, and readback and conversion turn a neutral of a
  singleton type (`Unit`, a Π into one, a Σ of two) into its one value. Its
  terms are elaborated bidirectionally, and every node but the universe
  carries its type as an annotation, which for a type says whether it is a
  singleton.
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
- The composed language converts to and from the monolith with free-foil's
  `foldAST`. The languages share scope resolution and parsing in
  `Demo.Parsing`.
- The library depends on free-foil 0.6.1 from Hackage. Its `mkFreeFoil`
  generates the bifunctor, `ZipMatchK`, `ZipMatchFoldK` and `NFData`
  instances of every generated signature, with `INLINE` pragmas, and the
  `NFData` instance of every generated pattern type. The generated modules
  carry no derive lines and no hand-written instances.
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
