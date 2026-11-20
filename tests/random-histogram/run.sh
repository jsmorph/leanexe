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
# argument, `0`, `abc`, `-5`, `+5`, or a 20-digit value above 2^64 must write nothing and exit
# with status 2.  A run with N of 1, 9, 10, 512, 513, 1000, or 1000000, with `007`, or with `5`
# followed by the argument `extra` must exit with status 0 and write ten lines, each a decimal
# count without a leading zero, whose sum is N, 7 for `007` and 5 for `5 extra`.  A run with N of
# 1000 and standard output /dev/full must exit with status 51, `nospc`, the errno of the write that
# failed.  No run may write to stderr.  A runner is a function `run_RUNNER OUT ARG...` that runs the
# command with the arguments ARG after the program name, writes its stdout to OUT and its stderr to
# OUT.stderr, and returns the command's status.
#
# On the native and QEMU runners, a run with N of 1000 appends its output to a file of 500 bytes
# under a file size limit, RLIMIT_FSIZE, of 512 bytes, with SIGXFSZ ignored.  Linux takes 12 bytes
# of the first write and fails the next with EFBIG, so the run must exit with status 22, `fbig`,
# and leave the file at 512 bytes, which end with 12 bytes of digits and newlines.  The Wasmtime
# host opens its standard output file itself, so this run has no Wasmtime case.
#
# When RUNNERS holds `native`, the executable then runs with N of 1000 under strace, which must
# show no call but getrandom, write, and exit_group, two getrandom calls with flags 0, of 4,096
# and 3,904 bytes, the 512 words of a full pass and the 488 words that remain, each answered with
# all of its bytes, and one write of the output's bytes that took all of them.  The run under the
# file size limit under strace must make two writes: the first returns 12, and the second offers
# 12 bytes fewer than the first and fails with EFBIG.  The run with N of 1000 checks that the first
# write offers the whole output.  A run with N of 1000 in which strace's injection makes the first
# getrandom return 100 without filling the buffer, a short count, must make three getrandom calls:
# 4,096 bytes at the buffer, which returns 100, the other 3,996 at the buffer's address plus 100,
# and 3,904 at the buffer, each of the last two answered with all of its bytes.  The first 12 words
# keep the buffer's initial zero bytes, so the run must exit with status 0 and write ten counts
# that sum to 1000, the first at least 12.  A run with `abc` under strace must make no call but
# exit_group.
# The file theorems of the executable are checked in tests/linux/a64-wasi.sh, which writes the
# executable from the same module with the same commands.
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

# refused RUNNER NAME ARG...: the run writes nothing to stdout or stderr and exits with status 2.
refused() {
  runner=$1
  name=$2
  shift 2
  stdout="$out/$runner-$name.stdout"
  status=0
  "run_$runner" "$stdout" "$@" || status=$?
  [ "$status" -eq 2 ] || fail "$runner $name" "status $status, expected 2"
  [ ! -s "$stdout" ] || fail "$runner $name" "output after a refusal"
  [ ! -s "$stdout.stderr" ] || fail "$runner $name" "output on stderr"
  cases=$((cases + 1))
}

# drawn RUNNER NAME N ARG...: the run exits with status 0, writes ten lines of decimal counts that
# sum to N, and writes nothing to stderr.
drawn() {
  runner=$1
  name=$2
  n=$3
  shift 3
  stdout="$out/$runner-$name.stdout"
  status=0
  "run_$runner" "$stdout" "$@" || status=$?
  [ "$status" -eq 0 ] || fail "$runner $name" "status $status"
  awk -v n="$n" '
    !/^(0|[1-9][0-9]*)$/ { bad = 1 }
    { sum += $0; lines++ }
    END { exit !(bad == 0 && lines == 10 && sum == n) }' "$stdout" ||
    fail "$runner $name" "output is not ten decimal counts that sum to $n"
  [ ! -s "$stdout.stderr" ] || fail "$runner $name" "output on stderr"
  cases=$((cases + 1))
}

# full RUNNER: the run with N of 1000 and standard output /dev/full exits with status 51 and writes
# nothing to stderr.
full() {
  runner=$1
  err="$out/$runner-full.stderr"
  status=0
  case $runner in
    wasm)
      timeout 600s "$host" --arg histogram --arg 1000 --stdout-file /dev/full run "$module" \
        2> "$err" || status=$? ;;
    native) timeout 600s "$elf" 1000 > /dev/full 2> "$err" || status=$? ;;
    qemu) timeout 600s "$qemu" "$elf" 1000 > /dev/full 2> "$err" || status=$? ;;
  esac
  [ "$status" -eq 51 ] || fail "$runner full" "status $status, expected 51"
  [ ! -s "$err" ] || fail "$runner full" "output on stderr"
  cases=$((cases + 1))
}

# limited RUNNER COMMAND...: COMMAND with the argument 1000 appends its output to a file of 500
# spaces under a file size limit of 512 bytes with SIGXFSZ ignored.  It must exit with status 22,
# write nothing to stderr, and leave the 500 spaces followed by 12 bytes of digits and newlines.
limited() {
  runner=$1
  shift
  file="$out/$runner-limited.stdout"
  printf '%500s' '' > "$file"
  status=0
  (trap '' XFSZ; ulimit -f 1; exec timeout 600s "$@" 1000 >> "$file" 2> "$file.stderr") ||
    status=$?
  [ "$status" -eq 22 ] || fail "$runner limited" "status $status, expected 22"
  [ "$(wc -c < "$file" | tr -d ' ')" -eq 512 ] ||
    fail "$runner limited" "the file does not hold 512 bytes"
  [ "$(head -c 500 "$file" | tr -d ' ' | wc -c | tr -d ' ')" -eq 0 ] ||
    fail "$runner limited" "the first 500 bytes changed"
  [ "$(tail -c 12 "$file" | tr -d '0123456789\n' | wc -c | tr -d ' ')" -eq 0 ] ||
    fail "$runner limited" "the last 12 bytes are not digits and newlines"
  [ ! -s "$file.stderr" ] || fail "$runner limited" "output on stderr"
  cases=$((cases + 1))
}

for runner in $RUNNERS; do
  full "$runner"
  case $runner in
    native) limited native "$elf" ;;
    qemu) limited qemu "$qemu" "$elf" ;;
  esac
  refused "$runner" none
  refused "$runner" zero 0
  refused "$runner" letters abc
  refused "$runner" negative -5
  refused "$runner" plus +5
  refused "$runner" overflow 99999999999999999999
  for n in 1 9 10 512 513 1000 1000000; do
    drawn "$runner" "$n" "$n" "$n"
  done
  drawn "$runner" zeros 7 007
  drawn "$runner" extra 5 5 extra
done

# calls TRACE: the calls of the trace that strace wrote to TRACE after the execve, sorted, each
# followed by a space.
calls() {
  sed -n '/^execve(/,$p' "$1" | tail -n +2 | sed '/^+++/d; s/(.*//' | sort -u | tr '\n' ' '
}

case " $RUNNERS " in
  *" native "*)
    trace="$out/native-1000.strace"
    status=0
    strace -e raw=getrandom -o "$trace" "$elf" 1000 > "$out/native-1000-strace.stdout" ||
      status=$?
    [ "$status" -eq 0 ] || fail strace "status $status"
    found=$(calls "$trace")
    [ "$found" = "exit_group getrandom write " ] || fail strace "the calls $found"
    requests=$(sed -n 's/^getrandom([^,]*, *\([^,]*\), *\([^)]*\)) *= *\([^ ]*\)$/\1 \2 \3/p' \
        "$trace" | while read -r count flags result; do
      printf '%d %d %d ' "$((count))" "$((flags))" "$((result))"
    done)
    [ "$requests" = "4096 0 4096 3904 0 3904 " ] ||
      fail strace "the getrandom calls (count, flags, result): $requests"
    size=$(wc -c < "$out/native-1000-strace.stdout" | tr -d ' ')
    writes=$(sed -n 's/^write(1, .*, \([0-9][0-9]*\)) *= *\(-\{0,1\}[0-9][0-9]*\).*$/\1 \2/p' \
      "$trace" | tr '\n' ' ')
    [ "$writes" = "$size $size " ] ||
      fail strace "the writes (count, result) $writes of an output of $size bytes"
    cases=$((cases + 1))
    trace="$out/native-short.strace"
    stdout="$out/native-short-strace.stdout"
    status=0
    strace -e raw=getrandom -e inject=getrandom:retval=100:when=1 -o "$trace" "$elf" 1000 \
      > "$stdout" || status=$?
    [ "$status" -eq 0 ] || fail "strace short" "status $status"
    awk '
      !/^(0|[1-9][0-9]*)$/ { bad = 1 }
      { sum += $0; lines++ }
      NR == 1 && $0 < 12 { bad = 1 }
      END { exit !(bad == 0 && lines == 10 && sum == 1000) }' "$stdout" ||
      fail "strace short" "output is not ten counts that sum to 1000, the first at least 12"
    requests=$(sed -n \
      's/^getrandom(\([^,]*\), *\([^,]*\), *\([^)]*\)) *= *\([-0-9a-fx]*\).*$/\1 \2 \3 \4/p' \
      "$trace" | while read -r address count flags result; do
      printf '%d %d %d %d ' "$((address))" "$((count))" "$((flags))" "$((result))"
    done)
    set -- $requests
    [ "$#" -eq 12 ] && [ "$5" -eq $(($1 + 100)) ] && [ "$9" -eq "$1" ] &&
      [ "$2 $3 $4 $6 $7 $8 ${10} ${11} ${12}" = "4096 0 100 3996 0 3996 3904 0 3904" ] ||
      fail "strace short" "the getrandom calls (address, count, flags, result): $requests"
    cases=$((cases + 1))
    trace="$out/native-limited.strace"
    file="$out/native-limited-strace.stdout"
    printf '%500s' '' > "$file"
    status=0
    (trap '' XFSZ; exec strace -e trace=write -o "$trace" sh -c 'ulimit -f 1; exec "$0" 1000' \
      "$elf" >> "$file") || status=$?
    [ "$status" -eq 22 ] || fail strace "status $status of the limited run"
    writes=$(sed -n 's/^write(1, .*, \([0-9][0-9]*\)) *= *\(-\{0,1\}[0-9][0-9]*\).*$/\1 \2/p' \
      "$trace" | tr '\n' ' ')
    set -- $writes
    [ "$#" -eq 4 ] && [ "$2" -eq 12 ] && [ "$3" -eq "$(($1 - 12))" ] && [ "$4" -eq -1 ] &&
      grep -q 'EFBIG' "$trace" ||
      fail strace "the writes (count, result) of the limited run: $writes"
    cases=$((cases + 1))
    trace="$out/native-letters.strace"
    status=0
    strace -o "$trace" "$elf" abc > "$out/native-letters-strace.stdout" || status=$?
    [ "$status" -eq 2 ] || fail strace "status $status of a refusal"
    found=$(calls "$trace")
    [ "$found" = "exit_group " ] || fail strace "the calls $found of a refusal"
    cases=$((cases + 1)) ;;
esac

printf 'random histogram: %s runs passed\n' "$cases"
