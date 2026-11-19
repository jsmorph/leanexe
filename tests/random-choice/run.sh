#!/bin/sh
# Checks the unbiased random choice of Demos/RandomChoice.  It checks the hashes of the reviewed
# specifications and samples against spec.sha256 and picks.sha256, builds the demo's modules,
# elaborates tests/random-choice/Axioms.lean, which restates the call theorems of the pure core,
# the counting theorems, and the theorems of the WASI command and fails on an axiom other than
# propext, Classical.choice, and Quot.sound, and emits and validates the command's module.
#
# It then runs the module in the Wasmtime host.  A run with no argument, with N alone, with N or K
# of 0, with letters, a sign, or a 20-digit value above 2^64 in either place must write nothing
# and exit with status 2.  A run of `choose N K` must exit with status 0 and write K lines, each a
# decimal value without a leading zero in [1, N], for N of 1, 6, 2^63 + 1, which rejects 2^63 - 1
# words of 2^64, and 2^64 - 1, with K up to 1,000,000, for `007 3`, and for `6 5 extra`.  The run
# with N of 6 and K of 1,000,000 must write each of the six values, and the run with N of 1 only
# the value 1.  A run with standard output /dev/full must exit with status 51, `nospc`, the errno
# of the write that failed.  No run may write to stderr.  The host draws its random bytes from the
# operating system, so no run checks the values beyond their range.  The run with N of
# 2^64 - 1 and K of 1,000,000 runs under `/usr/bin/time -v`, and the script prints its elapsed
# time and maximum resident set.
#
# The pure module's samples run in `tests/verified/run.sh --cases randomChoice`.
# Usage: tests/random-choice/run.sh
set -eu
set -f
if ! command -v wasm-tools > /dev/null 2>&1; then
  printf 'wasm-tools is not on the search path\n' >&2
  exit 1
fi
if [ ! -x /usr/bin/time ]; then
  printf 'Missing /usr/bin/time\n' >&2
  exit 1
fi

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
out="$root/build/random-choice"
host="$root/build/tools/leanexe-wasmtime-host"
module="$out/command.wasm"
mkdir -p "$out"

if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi

fail() {
  printf 'random choice %s: %s\n' "$1" "$2" >&2
  exit 1
}

sha256sum --quiet -c Demos/RandomChoice/spec.sha256 ||
  fail spec "Spec.lean or Samples.lean differs from the reviewed version"
sha256sum --quiet -c Demos/RandomChoice/picks.sha256 ||
  fail spec "PicksSpec.lean or PicksSamples.lean differs from the reviewed version"

tools/leanrun --timeout 60m --log "$out/build.log" lake build Demos.RandomChoice.Compiled \
  Demos.RandomChoice.Unbiased Demos.RandomChoice.CommandStart
tools/leanrun --timeout 10m lake env lean tests/random-choice/Axioms.lean
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Demos.RandomChoice.Command \
  Demos.RandomChoice.command.module "$module"
wasm-tools validate "$module"
printf 'module: %s bytes\n' "$(wc -c < "$module" | tr -d ' ')"

# run OUT ARG...: runs the module in the Wasmtime host with the program name `choose` and the
# arguments ARG, and returns its status.
run() {
  stdout=$1
  shift
  set -- choose "$@"
  count=$#
  for value in "$@"; do
    set -- "$@" --arg "$value"
  done
  shift "$count"
  timeout 600s "$host" "$@" --stdout-file "$stdout" run "$module" 2> "$stdout.stderr"
}

cases=0

# refused NAME ARG...: the run writes nothing to stdout or stderr and exits with status 2.
refused() {
  name=$1
  shift
  stdout="$out/$name.stdout"
  status=0
  run "$stdout" "$@" || status=$?
  [ "$status" -eq 2 ] || fail "$name" "status $status, expected 2"
  [ ! -s "$stdout" ] || fail "$name" "output after a refusal"
  [ ! -s "$stdout.stderr" ] || fail "$name" "output on stderr"
  cases=$((cases + 1))
}

# check NAME N K: the output of run NAME holds K lines, each a decimal value without a leading zero
# in [1, N], and the run wrote nothing to stderr.
check() {
  stdout="$out/$1.stdout"
  awk -v n="$2" -v k="$3" '
    function le(a, b) { return length(a) < length(b) || (length(a) == length(b) && a <= b) }
    !/^[1-9][0-9]*$/ || !le($0, n) { bad = 1 }
    { lines++ }
    END { exit !(bad == 0 && lines == k) }' "$stdout" ||
    fail "$1" "output is not $3 decimal values in [1, $2]"
  [ ! -s "$stdout.stderr" ] || fail "$1" "output on stderr"
}

# chosen NAME N K ARG...: the run exits with status 0 and writes K lines, each a decimal value
# without a leading zero in [1, N], and nothing to stderr.
chosen() {
  name=$1
  n=$2
  k=$3
  shift 3
  status=0
  run "$out/$name.stdout" "$@" || status=$?
  [ "$status" -eq 0 ] || fail "$name" "status $status"
  check "$name" "$n" "$k"
  cases=$((cases + 1))
}

refused none
refused alone 6
refused zero-n 0 5
refused zero-k 5 0
refused letters-n abc 5
refused letters-k 5 abc
refused negative -5 5
refused plus 5 +5
refused overflow-n 18446744073709551616 5
refused overflow-k 5 99999999999999999999

status=0
timeout 600s "$host" --arg choose --arg 6 --arg 1000 --stdout-file /dev/full run "$module" \
  2> "$out/full.stderr" || status=$?
[ "$status" -eq 51 ] || fail full "status $status, expected 51"
[ ! -s "$out/full.stderr" ] || fail full "output on stderr"
cases=$((cases + 1))

chosen one 1 10 1 10
chosen one-million 1 1000000 1 1000000
[ "$(sort -u "$out/one-million.stdout")" = 1 ] || fail one-million "a value other than 1"
chosen die 6 1000 6 1000
chosen half 9223372036854775809 100000 9223372036854775809 100000
chosen largest 18446744073709551615 1000 18446744073709551615 1000
chosen zeros 7 3 007 3
chosen extra 6 5 6 5 extra
chosen million 6 1000000 6 1000000
for v in 1 2 3 4 5 6; do
  grep -qx "$v" "$out/million.stdout" || fail million "no line holds $v"
done
chosen half-million 9223372036854775809 1000000 9223372036854775809 1000000

status=0
/usr/bin/time -v -o "$out/largest-million.time" timeout 600s "$host" --arg choose \
  --arg 18446744073709551615 --arg 1000000 --stdout-file "$out/largest-million.stdout" \
  run "$module" 2> "$out/largest-million.stdout.stderr" || status=$?
[ "$status" -eq 0 ] || fail largest-million "status $status"
check largest-million 18446744073709551615 1000000
cases=$((cases + 1))
sed -n 's/^[[:space:]]*\(Elapsed (wall clock) time.*\)$/largest-million: \1/p
  s/^[[:space:]]*\(Maximum resident set size.*\)$/largest-million: \1/p' \
  "$out/largest-million.time"

printf 'random choice: %s runs passed\n' "$cases"
