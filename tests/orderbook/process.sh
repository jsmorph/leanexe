#!/bin/sh
# Tests the native part of the order book's WASI process: the axiom audit of its proofs, the
# scripted-host runs of orderbook-process, and the streams of tests/orderbook/run.sh through
# orderbook-native, compared byte for byte with the event words that orderbook-compare checks
# against Spec.run and line for line with the Python reference's events, then ends of input and
# I/O errors.  Prints one summary line and exits with status 1 on any failure.
# Usage: tests/orderbook/process.sh
set -u
cd "$(dirname "$0")/../.." || exit 2

out=build/orderbook-process
tests=tests/orderbook
native=.lake/build/bin/orderbook-native
compare=.lake/build/bin/orderbook-compare
: "${UV_CACHE_DIR:=$(pwd)/build/orderbook/uv-cache}"
export UV_CACHE_DIR

command -v uv > /dev/null 2>&1 || { echo "process.sh: uv is not on the search path" >&2; exit 2; }
mkdir -p "$out/streams" "$out/ends" "$out/io" || exit 2

tools/leanrun --timeout 60m lake build Demos.OrderBook.ProcessCorrect orderbook-native \
  orderbook-process orderbook-compare || exit 1
tools/leanrun --timeout 10m lake env lean "$tests/ProcessAxioms.lean" || exit 1
.lake/build/bin/orderbook-process || exit 1
"$tests/run.sh" || exit 1

failures=0
fail() {
  failures=$((failures + 1))
  echo "process.sh: $*" >&2
}

# Runs the native process on stdin $1 with stdout $2 and stderr $3 and prints its status.
run_native() {
  status=0
  "$native" < "$1" > "$2" 2> "$3" || status=$?
  echo "$status"
}

streams=0
agreed=0
while read -r dir file next; do
  streams=$((streams + 1))
  stream=build/orderbook/$dir/$file
  base=$out/streams/$dir-${file%.bin}
  status=$(run_native "$stream" "$base.native" "$base.err")
  if [ "$status" -ne 0 ] || [ -s "$base.err" ]; then
    fail "$dir/$file: status $status: $(cat "$base.err")"
    continue
  fi
  if ! "$compare" events "$stream" "$base.expected" 2> "$base.compare"; then
    fail "$dir/$file: orderbook-compare: $(cat "$base.compare")"
    continue
  fi
  if ! cmp -s "$base.expected" "$base.native"; then
    fail "$dir/$file: stdout differs from the event words of Spec.run"
    continue
  fi
  reference=build/orderbook/results/$dir-${file%.bin}.python
  if [ "$next" != 1 ]; then
    reference=$base.python
    uv run "$tests/reference.py" "$stream" > "$reference" || {
      fail "$dir/$file: the Python reference failed"; continue; }
  fi
  grep '^event' "$reference" > "$base.reference-events"
  uv run "$tests/event_lines.py" "$base.native" > "$base.native-events" || {
    fail "$dir/$file: event_lines.py failed"; continue; }
  if cmp -s "$base.reference-events" "$base.native-events"; then
    agreed=$((agreed + 1))
  else
    fail "$dir/$file: stdout differs from the Python reference's events"
  fi
done < build/orderbook/list.txt

# Ends of input: no bytes, a final record of 1 to 6 whole words, and 1 to 7 bytes that fill no
# word after whole records, after whole words, and alone.  The expected output is that of the
# whole words, and the status is 0 for whole words and 28 otherwise.
ends=0
sample=build/orderbook/lean/sample-01.bin
words=build/orderbook/lean/sample-02.bin
expect_end() {
  # $1 name, $2 input, $3 whole words of the input, $4 expected status
  ends=$((ends + 1))
  status=$(run_native "$2" "$out/ends/$1.native" "$out/ends/$1.err")
  if [ "$status" -ne "$4" ] || [ -s "$out/ends/$1.err" ]; then
    fail "end $1: status $status, expected $4: $(cat "$out/ends/$1.err")"
    return
  fi
  if [ -s "$3" ]; then
    "$compare" events "$3" "$out/ends/$1.expected" 2> "$out/ends/$1.compare" || {
      fail "end $1: orderbook-compare: $(cat "$out/ends/$1.compare")"; return; }
  else
    : > "$out/ends/$1.expected"
  fi
  cmp -s "$out/ends/$1.expected" "$out/ends/$1.native" || fail "end $1: stdout differs"
}
: > "$out/ends/empty.bin"
expect_end empty "$out/ends/empty.bin" "$out/ends/empty.bin" 0
for k in 1 2 3 4 5 6; do
  { cat "$sample"; head -c $((8 * k)) "$words"; } > "$out/ends/words-$k.bin"
  expect_end "words-$k" "$out/ends/words-$k.bin" "$out/ends/words-$k.bin" 0
done
for t in 1 2 3 4 5 6 7; do
  head -c "$t" "$words" > "$out/ends/bytes-$t.bin"
  expect_end "bytes-$t" "$out/ends/bytes-$t.bin" "$out/ends/empty.bin" 28
  { cat "$sample"; head -c "$t" "$words"; } > "$out/ends/records-bytes-$t.bin"
  expect_end "records-bytes-$t" "$out/ends/records-bytes-$t.bin" "$sample" 28
  { cat "$out/ends/words-3.bin"; head -c "$t" "$words"; } > "$out/ends/words-bytes-$t.bin"
  expect_end "words-bytes-$t" "$out/ends/words-bytes-$t.bin" "$out/ends/words-3.bin" 28
done

# I/O errors: a directory as stdin fails the first read with EISDIR, and /dev/full as stdout fails
# the first write with ENOSPC.  The native adapter raises each as a Lean IO.Error and exits with
# status 1.
io=0
status=0
"$native" < / > "$out/io/read.stdout" 2> "$out/io/read.stderr" || status=$?
io=$((io + 1))
if [ "$status" -ne 1 ] || [ -s "$out/io/read.stdout" ] ||
    ! grep -q 'error code: 21' "$out/io/read.stderr"; then
  fail "read error: status $status: $(cat "$out/io/read.stderr")"
fi
if [ -e /dev/full ]; then
  status=0
  "$native" < "$sample" > /dev/full 2> "$out/io/write.stderr" || status=$?
  io=$((io + 1))
  if [ "$status" -ne 1 ] || ! grep -q 'error code: 28' "$out/io/write.stderr"; then
    fail "write error: status $status: $(cat "$out/io/write.stderr")"
  fi
fi

echo "orderbook process: $streams streams, $agreed agree with Spec.run and the Python reference," \
  "$ends ends of input, $io I/O errors, $failures failures"
[ "$failures" -eq 0 ]
