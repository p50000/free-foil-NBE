#!/usr/bin/env bash
# Measure the three columns as medians of N per-process runs.
#
# Each process benchmarks one column only, so the columns do not share a heap,
# and the column order rotates from run to run. Allocation figures need the
# RTS statistics (+RTS -T). Usage, from this directory, after `cabal build`:
#
#   ./medians.sh [results-dir]        # N=12 by default; override with N=...
set -euo pipefail
cd "$(dirname "$0")"

N=${N:-12}
OUT=${1:-results}
mkdir -p "$OUT"
# Remove the output of earlier runs, which would otherwise enter the medians.
rm -f "$OUT"/run*_col*.csv "$OUT"/run*_col*.log
BIN=$(cabal list-bin nbe-harness | tail -n1)
COLS=("NBE.FreeFoil (generic)" "NBE.FreeFoil (monomorphic)" "NBE.Foil")

for run in $(seq 1 "$N"); do
  for k in 0 1 2; do
    i=$(( (run + k) % 3 ))
    col="${COLS[$i]}"
    "$BIN" -p "\$NF == \"$col\"" --csv "$OUT/run${run}_col${i}.csv" +RTS -T -RTS \
      > "$OUT/run${run}_col${i}.log" 2>&1
    echo "run $run: $col"
  done
done

python3 - "$OUT" <<'EOF'
import csv, glob, os, statistics, sys

out = sys.argv[1]
data = {}
for path in glob.glob(os.path.join(out, "run*_col*.csv")):
    with open(path) as fh:
        for row in csv.DictReader(fh):
            t = int(row["Mean (ps)"])
            b = int(row.get("Allocated") or 0)
            data.setdefault(row["Name"], []).append((t, b))

def time_(ps):
    us = ps / 1e6
    return f"{us:.0f} µs" if us >= 100 else f"{us:.1f} µs"

def bytes_(b):
    return f"{b / 1e6:.1f} MB" if b >= 1e6 else f"{b / 1e3:.0f} KB"

print()
print(f"medians of {N} runs" if (N := len(next(iter(data.values())))) else "no data")
for name in sorted(data):
    ts = [t for t, _ in data[name]]
    bs = [b for _, b in data[name]]
    print(f"{name}: {time_(statistics.median(ts))}, {bytes_(statistics.median(bs))}")
EOF
