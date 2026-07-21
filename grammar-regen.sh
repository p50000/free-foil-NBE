#!/usr/bin/env bash
# Regenerate the BNFC lexer/parser/printer for the lambda-pi demo language
# from demo/grammar/Syntax.cf into gen/LambdaPi/Syntax/.
#
# Requires bnfc, alex, and happy on PATH:
#   cabal install BNFC alex happy
#
# The tools are run from gen/ with relative input paths so the {-# LINE #-}
# pragmas they embed are stable (reproducible output, no absolute paths).
set -euo pipefail
cd "$(dirname "$0")"

OUT=gen
rm -rf "$OUT/LambdaPi/Syntax"
bnfc --haskell -d -p LambdaPi -o "$OUT" demo/grammar/Syntax.cf
(
  cd "$OUT"
  alex  -o LambdaPi/Syntax/Lex.hs LambdaPi/Syntax/Lex.x
  happy -o LambdaPi/Syntax/Par.hs --ghc LambdaPi/Syntax/Par.y
)

# Keep only the modules the library actually compiles.
rm -f "$OUT"/LambdaPi/Syntax/ErrM.hs \
      "$OUT"/LambdaPi/Syntax/Skel.hs \
      "$OUT"/LambdaPi/Syntax/Test.hs \
      "$OUT"/LambdaPi/Syntax/Doc.txt \
      "$OUT"/LambdaPi/Syntax/Lex.x \
      "$OUT"/LambdaPi/Syntax/Par.y

echo "Regenerated $OUT/LambdaPi/Syntax/{Abs,Lex,Par,Print}.hs"
