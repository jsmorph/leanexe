#!/bin/sh
# Compares the order book's program with its specification and with the Python reference on the
# samples, the edge streams, and a fixed set of random streams, all written under build/orderbook.
# Prints one summary line and exits with status 1 on any failure.  Usage: tests/orderbook/run.sh
set -u
cd "$(dirname "$0")/../.." || exit 2

out=build/orderbook
tests=tests/orderbook
exe=.lake/build/bin/orderbook-compare
: "${UV_CACHE_DIR:=$(pwd)/$out/uv-cache}"
export UV_CACHE_DIR

command -v uv > /dev/null 2>&1 || { echo "run.sh: uv is not on the search path" >&2; exit 2; }
mkdir -p "$out/random" "$out/results" || exit 2

tools/leanrun --timeout 60m lake build orderbook-compare || exit 1
"$exe" write "$out/lean" || exit 1
uv run "$tests/make_edges.py" "$out/edges" || exit 1

list=$out/list.txt
: > "$list"
while read -r file next; do
  echo "lean $file $next" >> "$list"
done < "$out/lean/manifest.txt"
for f in "$out"/edges/*.bin; do
  echo "edges $(basename "$f") 1" >> "$list"
done

gen() {
  uv run "$tests/streams.py" --profile "$1" --seed "$2" --commands "$3" \
    --out "$out/random/$1-$2-$3.bin" || exit 1
  echo "random $1-$2-$3.bin 1" >> "$list"
}
for profile in mixed edges truncated; do
  gen "$profile" 1 1000
  gen "$profile" 2 1000
  gen "$profile" 3 1000
  gen "$profile" 4 10000
  gen "$profile" 5 100000
done
gen full 1 6000
gen full 2 6000
gen full 3 20000
gen full 4 100000

streams=0
spec=0
python=0
compared=0
failures=0
while read -r dir file next; do
  streams=$((streams + 1))
  stream=$out/$dir/$file
  result=$out/results/$dir-${file%.bin}
  if "$exe" stream "$stream" "$next" > "$result.lean" 2> "$result.err"; then
    spec=$((spec + 1))
  else
    failures=$((failures + 1))
    echo "run.sh: $dir/$file disagrees with the specification: $(cat "$result.err")" >&2
    continue
  fi
  [ "$next" = 1 ] || continue
  compared=$((compared + 1))
  if ! uv run "$tests/reference.py" "$stream" > "$result.python"; then
    failures=$((failures + 1))
    echo "run.sh: $dir/$file: the Python reference failed" >&2
  elif cmp -s "$result.lean" "$result.python"; then
    python=$((python + 1))
  else
    failures=$((failures + 1))
    echo "run.sh: $dir/$file differs from the Python reference" >&2
  fi
done < "$list"

echo "orderbook: $streams streams, $spec agree with the specification, $python of $compared" \
  "agree with the Python reference, $failures failures"
[ "$failures" -eq 0 ]
