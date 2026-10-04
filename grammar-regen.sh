#!/usr/bin/env bash
# Regenerate the BNFC lexers/parsers/printers for the demo languages
# from demo/grammar/*.cf into gen/<Lang>/Syntax/.
#
# Requires bnfc, alex, and happy on PATH:
#   cabal install BNFC alex happy
#
# The tools are run from gen/ with relative input paths so the {-# LINE #-}
# pragmas they embed are stable (reproducible output, no absolute paths).
set -euo pipefail
cd "$(dirname "$0")"

OUT=gen

# Each language keeps its grammar at demo/grammar/<Lang>/Syntax.cf; the file
# must be called Syntax.cf because BNFC names the generated module after it.
GRAMMARS=(
  "LambdaPi demo/grammar/LambdaPi/Syntax.cf"
  "LambdaLet demo/grammar/LambdaLet/Syntax.cf"
)

for entry in "${GRAMMARS[@]}"; do
  read -r LANG_PREFIX GRAMMAR <<< "$entry"
  rm -rf "$OUT/$LANG_PREFIX/Syntax"
  bnfc --haskell -d -p "$LANG_PREFIX" -o "$OUT" "$GRAMMAR"
  (
    cd "$OUT"
    alex  -o "$LANG_PREFIX/Syntax/Lex.hs" "$LANG_PREFIX/Syntax/Lex.x"
    happy -o "$LANG_PREFIX/Syntax/Par.hs" --ghc "$LANG_PREFIX/Syntax/Par.y"
  )

  # Keep only the modules the libraries actually compile.
  rm -f "$OUT/$LANG_PREFIX"/Syntax/ErrM.hs \
        "$OUT/$LANG_PREFIX"/Syntax/Skel.hs \
        "$OUT/$LANG_PREFIX"/Syntax/Test.hs \
        "$OUT/$LANG_PREFIX"/Syntax/Doc.txt \
        "$OUT/$LANG_PREFIX"/Syntax/Lex.x \
        "$OUT/$LANG_PREFIX"/Syntax/Par.y

  echo "Regenerated $OUT/$LANG_PREFIX/Syntax/{Abs,Lex,Par,Print}.hs"
done
