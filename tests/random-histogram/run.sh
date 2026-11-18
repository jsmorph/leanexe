#!/bin/sh
# Checks the random-residue histogram of Demos/RandomHistogram.  It builds the demo's modules,
# checks the hashes of the reviewed specification and samples against spec.sha256, elaborates
# tests/random-histogram/Axioms.lean, which restates the call theorems of the pure core and the
# theorem of the WASI command and fails on an axiom other than propext, Classical.choice, and
# Quot.sound, and emits and validates the command's module.  It writes the module's AArch64 Linux
# executable with `a64-wasi wasm`, which fails when genWasiElf rejects the module.
#
# It then runs the command with each runner of RUNNERS, by default `wasm native qemu`: the module in
# the Wasmtime host, the executable on the host's processor, which must be AArch64 Linux, and the
# executable under qemu-aarch64, QEMU's user-mode emulator, or QEMU_USER when set.  A run with no
# argument, `0`, `abc`, `-5`, or a 20-digit value above 2^64 must write nothing and exit with
# status 2.  A run with N of 1, 9, 10, 512, 513, 1000, or 1000000 must exit with status 0 and write
# ten lines, each a decimal count without a leading zero, whose sum is N.  A runner is a function
# `run_RUNNER OUT ARG...` that runs the command with the arguments ARG after the program name,
# writes its stdout to OUT, and returns the command's status.
#
# When RUNNERS holds `native`, the executable then runs with N of 1000 under strace, which must
# show no call but getrandom, write, and exit_group, and two getrandom calls with flags 0, of 4,096
# and 3,904 bytes, the 512 words of a full pass and the 488 words that remain, each answered with
# all of its bytes.  The file theorems of the executable are checked in tests/linux/a64-wasi.sh.
#
# The pure module's samples run in `tests/verified/run.sh --cases randomHistogram`.
# Usage: tests/random-histogram/run.sh
set -eu
set -f
if ! command -v wasm-tools > /dev/null 2>&1; then
  printf 'wasm-tools is not on the search path\n' >&2
  exit 1
fi
RUNNERS=${RUNNERS:-wasm native qemu}
qemu=${QEMU_USER:-/usr/bin/qemu-aarch64}
for runner in $RUNNERS; do
  case $runner in
    native)
      if [ "$(uname -s) $(uname -m)" != "Linux aarch64" ]; then
        printf 'the native runner needs an AArch64 Linux host\n' >&2
        exit 1
      fi
      if ! command -v strace > /dev/null 2>&1; then
        printf 'strace is not on the search path\n' >&2
        exit 1
      fi ;;
    qemu)
      if [ ! -x "$qemu" ]; then
        printf 'Missing QEMU user-mode emulator: %s\n' "$qemu" >&2
        exit 1
      fi ;;
  esac
done

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
out="$root/build/random-histogram"
host="$root/build/tools/leanexe-wasmtime-host"
module="$out/command.wasm"
elf="$out/command.elf"
mkdir -p "$out"

if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi

fail() {
  printf 'random histogram %s: %s\n' "$1" "$2" >&2
  exit 1
}

sha256sum --quiet -c Demos/RandomHistogram/spec.sha256 ||
  fail spec "Spec.lean or Samples.lean differs from the reviewed version"

tools/leanrun --timeout 60m --log "$out/build.log" lake build Demos.RandomHistogram.Compiled \
  Demos.RandomHistogram.CommandStart a64-wasi
tools/leanrun --timeout 10m lake env lean tests/random-histogram/Axioms.lean
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Demos.RandomHistogram.Command \
  Demos.RandomHistogram.command.module "$module"
wasm-tools validate "$module"
tools/leanrun --timeout 10m lake env .lake/build/bin/a64-wasi wasm "$module" "$elf" ||
  fail elf "genWasiElf rejects the module"
chmod +x "$elf"
printf 'genWasiElf: %s bytes\n' "$(wc -c < "$elf" | tr -d ' ')"

# run_wasm OUT ARG...: runs the module in the Wasmtime host with the program name `histogram` and
# the arguments ARG, and returns its status.
run_wasm() {
  stdout=$1
  shift
  set -- histogram "$@"
  count=$#
  for value in "$@"; do
    set -- "$@" --arg "$value"
  done
  shift "$count"
  timeout 600s "$host" "$@" --stdout-file "$stdout" run "$module" 2> "$stdout.stderr"
}

# run_native OUT ARG...: runs the executable on the host's processor with the arguments ARG.
run_native() {
  stdout=$1
  shift
  timeout 600s "$elf" "$@" > "$stdout" 2> "$stdout.stderr"
}

# run_qemu OUT ARG...: runs the executable under QEMU's user-mode emulator with the arguments ARG.
run_qemu() {
  stdout=$1
  shift
  timeout 600s "$qemu" "$elf" "$@" > "$stdout" 2> "$stdout.stderr"
}

cases=0

# refused RUNNER NAME ARG...: the run writes nothing and exits with status 2.
refused() {
  runner=$1
  name=$2
  shift 2
  stdout="$out/$runner-$name.stdout"
  status=0
  "run_$runner" "$stdout" "$@" || status=$?
  [ "$status" -eq 2 ] || fail "$runner $name" "status $status, expected 2"
  [ ! -s "$stdout" ] || fail "$runner $name" "output after a refusal"
  cases=$((cases + 1))
}

# drawn RUNNER N: the run exits with status 0 and writes ten lines of decimal counts that sum to N.
drawn() {
  runner=$1
  n=$2
  stdout="$out/$runner-$n.stdout"
  status=0
  "run_$runner" "$stdout" "$n" || status=$?
  [ "$status" -eq 0 ] || fail "$runner $n" "status $status"
  awk -v n="$n" '
    !/^(0|[1-9][0-9]*)$/ { bad = 1 }
    { sum += $0; lines++ }
    END { exit !(bad == 0 && lines == 10 && sum == n) }' "$stdout" ||
    fail "$runner $n" "output is not ten decimal counts that sum to $n"
  cases=$((cases + 1))
}

for runner in $RUNNERS; do
  refused "$runner" none
  refused "$runner" zero 0
  refused "$runner" letters abc
  refused "$runner" negative -5
  refused "$runner" overflow 99999999999999999999
  for n in 1 9 10 512 513 1000 1000000; do
    drawn "$runner" "$n"
  done
done

case " $RUNNERS " in
  *" native "*)
    trace="$out/native-1000.strace"
    status=0
    strace -e raw=getrandom -o "$trace" "$elf" 1000 > "$out/native-1000-strace.stdout" ||
      status=$?
    [ "$status" -eq 0 ] || fail strace "status $status"
    calls=$(sed -n '/^execve(/,$p' "$trace" | tail -n +2 | sed '/^+++/d; s/(.*//' | sort -u |
      tr '\n' ' ')
    [ "$calls" = "exit_group getrandom write " ] || fail strace "the calls $calls"
    requests=$(sed -n 's/^getrandom([^,]*, *\([^,]*\), *\([^)]*\)) *= *\([^ ]*\)$/\1 \2 \3/p' \
        "$trace" | while read -r count flags result; do
      printf '%d %d %d ' "$((count))" "$((flags))" "$((result))"
    done)
    [ "$requests" = "4096 0 4096 3904 0 3904 " ] ||
      fail strace "the getrandom calls (count, flags, result): $requests"
    cases=$((cases + 1)) ;;
esac

printf 'random histogram: %s runs passed\n' "$cases"
