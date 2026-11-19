#!/bin/sh
# Checks the unbiased random choice of Demos/RandomChoice.  It checks the hashes of the reviewed
# specifications and samples against spec.sha256 and picks.sha256, builds the demo's modules,
# elaborates tests/random-choice/Axioms.lean, which restates the call theorems of the pure core,
# the counting theorems, and the theorems of the WASI command and of its Linux runs and fails on an
# axiom other than propext, Classical.choice, and Quot.sound, and emits and validates the command's
# module.  It writes the module's AArch64 Linux executable with `a64-wasi wasm`, which fails when
# genWasiElf rejects the module.  With BUILD=no it skips these steps and runs the module and the
# executable in build/random-choice, which an earlier run wrote.
#
# It then runs the command with each runner of RUNNERS, by default `wasm native qemu`: the module in
# the Wasmtime host, the executable on the host's processor, which must be AArch64 Linux, and the
# executable under qemu-aarch64, QEMU's user-mode emulator, or QEMU_USER when set.  A runner is a
# function `run_RUNNER OUT ARG...` that runs the command with the arguments ARG after the program
# name, writes its stdout to OUT and its stderr to OUT.stderr, and returns the command's status.
# A run with no argument, with N alone, with N or K of 0, with letters, a sign, or a 20-digit value
# above 2^64 in either place must write nothing and exit with status 2.  A run of
# `choose N K` must exit with status 0 and write K lines, each a decimal value without a leading
# zero in [1, N], for N of 1, 6, 2^63 + 1, which rejects 2^63 - 1 words of 2^64, and 2^64 - 1, with
# K up to 1,000,000, for `007 3`, and for `6 5 extra`.  The run with N of 6 and K of 1,000,000 must
# write each of the six values, and the run with N of 1 only the value 1.  A run with standard
# output /dev/full must exit with status 51, `nospc`, the errno of the write that failed.  No run
# may write to stderr.  The runs draw their random bytes from the operating system, so no run
# checks the values beyond their range.  The run with N of 2^64 - 1 and K of 1,000,000 runs under
# `/usr/bin/time -v`, and the script prints its elapsed time and maximum resident set.
#
# On the native and QEMU runners, a run of `choose 6 1000` appends its output to a file of 500
# bytes under a file size limit, RLIMIT_FSIZE, of 512 bytes, with SIGXFSZ ignored.  Linux takes 12
# bytes of the first write and fails the next with EFBIG, so the run must exit with status 22,
# `fbig`, and leave the file at 512 bytes, which end with 12 bytes of digits and newlines.  The
# Wasmtime host opens its standard output file itself, so this run has no Wasmtime case.
#
# When RUNNERS holds `native`, the executable runs under strace with undecoded arguments, and the
# check fails when it cannot read a getrandom or write line.  The runs of `choose 6 1000` and
# `choose 18446744073709551615 100000` must make no call but getrandom, write, and exit_group.
# Every getrandom must pass the address of the first, 4,096 bytes, and flags 0, and return 4,096.
# Every write must be of descriptor 1, offer at least one byte, and return its count.  The first
# write of each pass, the write after a getrandom, must pass the address of the run's first write,
# the output buffer's, and each later write of the pass that address plus the bytes that the pass's
# writes took before it, offering the bytes that they did not take; since every write returns its
# count, each pass makes one write.  The results of the writes must sum to the output's size.  The
# first run must make, in order, a getrandom, a write of 1,024 bytes, a getrandom, and a write of
# 976 bytes, since N of 6 rejects 4 words of 2^64.  The run under the file size limit must make two
# writes of descriptor 1 from the address of the first run's writes: the first offers 1,024 bytes
# and returns 12, and the second passes the address plus 12, offers 1,012 bytes, and fails with
# EFBIG.  Two runs replace replies with strace's injection, and each meets `Full` of
# Demos/RandomHistogram/NativeCounts.lean.  In `choose 6 1000` with every getrandom returning 4,096
# without filling the buffer, the draw buffer keeps its initial zero bytes, and N of 6 rejects the
# word 0, so the run must reach the cap: ten getrandom calls into the draw buffer, the `passes` of
# K = 1,000, no write, and status 77.  In `choose 6 1` with every write returning 0, the run must
# make a getrandom of 4,096 bytes and three writes of descriptor 1 of the line's 2 bytes from one
# address, the passes of `writeAll`, and exit with status 78 with nothing written.  A run with
# `abc` must make no call but exit_group.  The file theorems of the executable are checked in
# tests/linux/a64-wasi.sh, which writes the executable from the same module with the same commands.
#
# The pure module's samples run in `tests/verified/run.sh --cases randomChoice`.
# Usage: tests/random-choice/run.sh
set -eu
set -f
RUNNERS=${RUNNERS:-wasm native qemu}
BUILD=${BUILD:-yes}
qemu=${QEMU_USER:-/usr/bin/qemu-aarch64}
if [ "$BUILD" = yes ] && ! command -v wasm-tools > /dev/null 2>&1; then
  printf 'wasm-tools is not on the search path\n' >&2
  exit 1
fi
if [ ! -x /usr/bin/time ]; then
  printf 'Missing /usr/bin/time\n' >&2
  exit 1
fi
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
out="$root/build/random-choice"
host="$root/build/tools/leanexe-wasmtime-host"
module="$out/command.wasm"
elf="$out/command.elf"
mkdir -p "$out"

case " $RUNNERS " in
  *" wasm "*)
    if [ ! -x "$host" ]; then
      printf 'Missing native host: %s\n' "$host" >&2
      exit 1
    fi ;;
esac

fail() {
  printf 'random choice %s: %s\n' "$1" "$2" >&2
  exit 1
}

if [ "$BUILD" = yes ]; then
  sha256sum --quiet -c Demos/RandomChoice/spec.sha256 ||
    fail spec "Spec.lean or Samples.lean differs from the reviewed version"
  sha256sum --quiet -c Demos/RandomChoice/picks.sha256 ||
    fail spec "PicksSpec.lean or PicksSamples.lean differs from the reviewed version"

  tools/leanrun --timeout 60m --log "$out/build.log" lake build Demos.RandomChoice.Compiled \
    Demos.RandomChoice.Unbiased Demos.RandomChoice.Budget Demos.RandomChoice.Output \
    Demos.RandomChoice.NativeChoices a64-wasi
  tools/leanrun --timeout 10m lake env lean tests/random-choice/Axioms.lean
  tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Demos.RandomChoice.Command \
    Demos.RandomChoice.command.module "$module"
  wasm-tools validate "$module"
  tools/leanrun --timeout 10m lake env .lake/build/bin/a64-wasi wasm "$module" "$elf" ||
    fail elf "genWasiElf rejects the module"
  chmod +x "$elf"
fi
case " $RUNNERS " in
  *" wasm "*) [ -f "$module" ] || fail module "missing $module" ;;
esac
case " $RUNNERS " in
  *" native "* | *" qemu "*) [ -x "$elf" ] || fail elf "missing $elf" ;;
esac
[ ! -f "$module" ] || printf 'module: %s bytes\n' "$(wc -c < "$module" | tr -d ' ')"
[ ! -f "$elf" ] ||
  printf 'executable: %s bytes, SHA-256 %s\n' "$(wc -c < "$elf" | tr -d ' ')" \
    "$(sha256sum "$elf" | cut -d ' ' -f 1)"

# run_wasm OUT ARG...: runs the module in the Wasmtime host with the program name `choose` and the
# arguments ARG, and returns its status.
run_wasm() {
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

# check NAME FILE N K: FILE holds K lines, each a decimal value without a leading zero in [1, N],
# and FILE.stderr is empty.
check() {
  awk -v n="$3" -v k="$4" '
    function le(a, b) { return length(a) < length(b) || (length(a) == length(b) && a <= b) }
    !/^[1-9][0-9]*$/ || !le($0, n) { bad = 1 }
    { lines++ }
    END { exit !(bad == 0 && lines == k) }' "$2" ||
    fail "$1" "output is not $4 decimal values in [1, $3]"
  [ ! -s "$2.stderr" ] || fail "$1" "output on stderr"
}

# chosen RUNNER NAME N K ARG...: the run exits with status 0 and writes K lines, each a decimal
# value without a leading zero in [1, N], and nothing to stderr.
chosen() {
  runner=$1
  name=$2
  n=$3
  k=$4
  shift 4
  stdout="$out/$runner-$name.stdout"
  status=0
  "run_$runner" "$stdout" "$@" || status=$?
  [ "$status" -eq 0 ] || fail "$runner $name" "status $status"
  check "$runner $name" "$stdout" "$n" "$k"
  cases=$((cases + 1))
}

# full RUNNER: the run of `choose 6 1000` with standard output /dev/full exits with status 51 and
# writes nothing to stderr.
full() {
  runner=$1
  err="$out/$runner-full.stderr"
  status=0
  case $runner in
    wasm)
      timeout 600s "$host" --arg choose --arg 6 --arg 1000 --stdout-file /dev/full run "$module" \
        2> "$err" || status=$? ;;
    native) timeout 600s "$elf" 6 1000 > /dev/full 2> "$err" || status=$? ;;
    qemu) timeout 600s "$qemu" "$elf" 6 1000 > /dev/full 2> "$err" || status=$? ;;
  esac
  [ "$status" -eq 51 ] || fail "$runner full" "status $status, expected 51"
  [ ! -s "$err" ] || fail "$runner full" "output on stderr"
  cases=$((cases + 1))
}

# limited RUNNER COMMAND...: COMMAND with the arguments 6 and 1000 appends its output to a file of
# 500 spaces under a file size limit of 512 bytes with SIGXFSZ ignored.  It must exit with status
# 22, write nothing to stderr, and leave the 500 spaces followed by 12 bytes of digits and newlines.
limited() {
  runner=$1
  shift
  file="$out/$runner-limited.stdout"
  printf '%500s' '' > "$file"
  status=0
  (trap '' XFSZ; ulimit -f 1; exec timeout 600s "$@" 6 1000 >> "$file" 2> "$file.stderr") ||
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

# timed RUNNER: the run of `choose 18446744073709551615 1000000` under /usr/bin/time -v exits with
# status 0 and writes 1,000,000 values in range, and the script prints its elapsed time and maximum
# resident set.
timed() {
  runner=$1
  stdout="$out/$runner-largest-million.stdout"
  set -- /usr/bin/time -v -o "$out/$runner-largest-million.time" timeout 600s
  case $runner in
    wasm) set -- "$@" "$host" --arg choose --arg 18446744073709551615 --arg 1000000 \
      --stdout-file "$stdout" run "$module" ;;
    native) set -- "$@" "$elf" 18446744073709551615 1000000 ;;
    qemu) set -- "$@" "$qemu" "$elf" 18446744073709551615 1000000 ;;
  esac
  status=0
  case $runner in
    wasm) "$@" 2> "$stdout.stderr" || status=$? ;;
    *) "$@" > "$stdout" 2> "$stdout.stderr" || status=$? ;;
  esac
  [ "$status" -eq 0 ] || fail "$runner largest-million" "status $status"
  check "$runner largest-million" "$stdout" 18446744073709551615 1000000
  cases=$((cases + 1))
  sed -n "s/^[[:space:]]*\(Elapsed (wall clock) time.*\)$/$runner largest-million: \1/p
    s/^[[:space:]]*\(Maximum resident set size.*\)$/$runner largest-million: \1/p" \
    "$out/$runner-largest-million.time"
}

for runner in $RUNNERS; do
  full "$runner"
  case $runner in
    native) limited native "$elf" ;;
    qemu) limited qemu "$qemu" "$elf" ;;
  esac
  refused "$runner" none
  refused "$runner" alone 6
  refused "$runner" zero-n 0 5
  refused "$runner" zero-k 5 0
  refused "$runner" letters-n abc 5
  refused "$runner" letters-k 5 abc
  refused "$runner" negative -5 5
  refused "$runner" plus 5 +5
  refused "$runner" overflow-n 18446744073709551616 5
  refused "$runner" overflow-k 5 99999999999999999999
  chosen "$runner" one 1 10 1 10
  chosen "$runner" one-million 1 1000000 1 1000000
  [ "$(sort -u "$out/$runner-one-million.stdout")" = 1 ] ||
    fail "$runner one-million" "a value other than 1"
  chosen "$runner" die 6 1000 6 1000
  chosen "$runner" half 9223372036854775809 100000 9223372036854775809 100000
  chosen "$runner" largest 18446744073709551615 1000 18446744073709551615 1000
  chosen "$runner" zeros 7 3 007 3
  chosen "$runner" extra 6 5 6 5 extra
  chosen "$runner" million 6 1000000 6 1000000
  for v in 1 2 3 4 5 6; do
    grep -qx "$v" "$out/$runner-million.stdout" || fail "$runner million" "no line holds $v"
  done
  chosen "$runner" half-million 9223372036854775809 1000000 9223372036854775809 1000000
  timed "$runner"
done

# after TRACE: the lines of the trace that strace wrote to TRACE after the last execve.
after() {
  sed -n '/^execve(/h; /^execve(/!H; ${x;p;}' "$1" | tail -n +2
}

# calls TRACE: the calls of TRACE after the last execve, sorted, each followed by a space.
calls() {
  after "$1" | sed '/^+++/d; /^---/d; s/(.*//' | sort -u | tr '\n' ' '
}

# passes TRACE: the getrandom and write calls of TRACE after the last execve, one a line, as the
# call's name and its decimal arguments and result, with -1 for a failed call: the address, count,
# flags, and result of a getrandom, and the address, count, descriptor, and result of a write.
# Fails when a getrandom or write line does not have that form.
passes() {
  after "$1" > "$1.after"
  number='\(0x[0-9a-f]*\|0\)'
  sed -n "s/^getrandom($number, *$number, *$number) *= *\([-0-9a-fx]*\).*\$/getrandom \1 \2 \3 \4/p
    s/^write($number, *$number, *$number) *= *\([-0-9a-fx]*\).*\$/write \2 \3 \1 \4/p" \
    "$1.after" |
    while read -r name address count third result; do
      printf '%s %d %d %d %d\n' "$name" "$((address))" "$((count))" "$((third))" "$((result))"
    done > "$1.calls"
  [ "$(grep -c '^\(getrandom\|write\)(' "$1.after")" -eq "$(wc -l < "$1.calls" | tr -d ' ')" ] ||
    fail strace "a getrandom or write of $1 that the check does not read"
}

# traced NAME TRACE OUTPUT: the calls of TRACE are getrandom, write, and exit_group.  Every
# getrandom passes the address of the first, 4,096 bytes, and flags 0, and returns 4,096.  Every
# write is of descriptor 1, offers at least one byte, and returns its count.  The first write after
# each getrandom passes the address of the run's first write, the output buffer's, and each later
# write of the pass that address plus the bytes that the pass's writes took before it and offers
# the bytes that they did not take.  The results of the writes sum to the size of OUTPUT.  Prints
# the calls in order, `g` for a getrandom and the count of each write.
traced() {
  found=$(calls "$2")
  [ "$found" = "exit_group getrandom write " ] || fail "strace $1" "the calls $found"
  passes "$2"
  summary=$(awk -v size="$(wc -c < "$3" | tr -d ' ')" '
    $1 == "getrandom" {
      if (draw == "") draw = $2
      if ($2 != draw || $3 != 4096 || $4 != 0 || $5 != 4096) { bad = "getrandom " NR; exit }
      draws++; taken = 0; left = -1; order = order " g"
    }
    $1 == "write" {
      if (buffer == "") buffer = $2
      if ($4 != 1 || $3 < 1 || $5 != $3 || draws == 0 || $2 != buffer + taken ||
          (left >= 0 && $3 != left)) { bad = "write " NR; exit }
      left = $3 - $5; taken += $5; total += $5; order = order " " $3
    }
    END {
      if (bad == "" && total != size) bad = "bytes " total
      if (bad != "") { print bad; exit 1 }
      print substr(order, 2)
    }' "$2.calls") ||
    fail "strace $1" "the call or total at $summary"
  printf '%s\n' "$summary"
}

case " $RUNNERS " in
  *" native "*)
    trace="$out/native-die.strace"
    status=0
    strace -e raw=getrandom,write -o "$trace" "$elf" 6 1000 > "$out/native-die-strace.stdout" ||
      status=$?
    [ "$status" -eq 0 ] || fail "strace die" "status $status"
    check "strace die" "$out/native-die-strace.stdout" 6 1000
    summary=$(traced die "$trace" "$out/native-die-strace.stdout")
    [ "$summary" = "g 1024 g 976" ] ||
      fail "strace die" "the calls $summary, expected g 1024 g 976"
    buffer=$(awk '$1 == "write" { print $2; exit }' "$trace.calls")
    draw=$(awk '$1 == "getrandom" { print $2; exit }' "$trace.calls")
    cases=$((cases + 1))
    trace="$out/native-largest.strace"
    status=0
    strace -e raw=getrandom,write -o "$trace" "$elf" 18446744073709551615 100000 \
      > "$out/native-largest-strace.stdout" || status=$?
    [ "$status" -eq 0 ] || fail "strace largest" "status $status"
    check "strace largest" "$out/native-largest-strace.stdout" 18446744073709551615 100000
    traced largest "$trace" "$out/native-largest-strace.stdout" > /dev/null
    cases=$((cases + 1))
    trace="$out/native-limited.strace"
    file="$out/native-limited-strace.stdout"
    printf '%500s' '' > "$file"
    status=0
    (trap '' XFSZ; exec strace -e raw=getrandom,write -o "$trace" \
      sh -c 'ulimit -f 1; exec "$0" 6 1000' "$elf" >> "$file") || status=$?
    [ "$status" -eq 22 ] || fail strace "status $status of the limited run"
    passes "$trace"
    writes=$(awk '$1 == "write" { printf "%d %d %d %d ", $4, $2, $3, $5 }' "$trace.calls")
    [ "$writes" = "1 $buffer 1024 12 1 $((buffer + 12)) 1012 -1 " ] && grep -q 'EFBIG' "$trace" ||
      fail strace "the writes (descriptor, address, count, result) of the limited run: $writes"
    cases=$((cases + 1))
    trace="$out/native-cap.strace"
    status=0
    strace -e raw=getrandom,write -e inject=getrandom:retval=4096 -o "$trace" "$elf" 6 1000 \
      > "$out/native-cap-strace.stdout" || status=$?
    [ "$status" -eq 77 ] || fail "strace cap" "status $status, expected 77"
    [ ! -s "$out/native-cap-strace.stdout" ] || fail "strace cap" "output at the cap"
    found=$(calls "$trace")
    [ "$found" = "exit_group getrandom " ] || fail "strace cap" "the calls $found"
    passes "$trace"
    draws=$(awk -v draw="$draw" '$2 == draw && $3 == 4096 && $4 == 0 && $5 == 4096 { n++ }
      END { print n + 0 }' "$trace.calls")
    [ "$draws" -eq 10 ] && [ "$(wc -l < "$trace.calls" | tr -d ' ')" -eq 10 ] ||
      fail "strace cap" "$draws getrandom calls of 4,096 bytes into the draw buffer, expected 10"
    cases=$((cases + 1))
    trace="$out/native-stalled.strace"
    status=0
    strace -e raw=getrandom,write -e inject=write:retval=0 -o "$trace" "$elf" 6 1 \
      > "$out/native-stalled-strace.stdout" || status=$?
    [ "$status" -eq 78 ] || fail "strace stalled" "status $status, expected 78"
    [ ! -s "$out/native-stalled-strace.stdout" ] || fail "strace stalled" "output after a stall"
    passes "$trace"
    found=$(awk '{ printf "%s %d %d %d %d ", $1, $2, $3, $4, $5 }' "$trace.calls")
    first=$(awk '$1 == "write" { print $2; exit }' "$trace.calls")
    want="getrandom $(awk '{ print $2; exit }' "$trace.calls") 4096 0 4096 "
    for i in 1 2 3; do want="${want}write $first 2 1 0 "; done
    [ "$found" = "$want" ] || fail "strace stalled" "the calls $found"
    cases=$((cases + 1))
    trace="$out/native-letters.strace"
    status=0
    strace -o "$trace" "$elf" abc 5 > "$out/native-letters-strace.stdout" || status=$?
    [ "$status" -eq 2 ] || fail strace "status $status of a refusal"
    found=$(calls "$trace")
    [ "$found" = "exit_group " ] || fail strace "the calls $found of a refusal"
    cases=$((cases + 1)) ;;
esac

printf 'random choice: %s runs passed\n' "$cases"
