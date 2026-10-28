#!/usr/bin/env bash
# The cases of tests/native/verified.sh under QEMU's virt machine for AArch64, without libc or an
# operating system (docs/native-bare-metal.md, milestone B1).  native-verified writes the C text,
# the glue, and the exports of each module of tests/verified/modules.txt.  CompCert compiles
# them, each translation with -fno-common, as tools/baremetal/build.sh compiles its inputs, with
# tools/native-host.c, whose main becomes host_main, and with the C library of
# tools/baremetal/libc, and tools/baremetal/build.sh links them with the startup code and a stack
# of STACK_SIZE bytes, 0x400000 by default.  The host reads its command line from a block that
# QEMU's generic loader places at 0x7F000000.  Each case runs in its own QEMU process, JOBS at a
# time (4 by default), under the rules of tests/native/verified.sh for results, traps, and
# allocation counters, and the module cases of euler and of shapes on sums under the rules of
# tests/modules/run.sh.  A case also fails when it reports an exception or a stack high-water mark
# of the whole stack.  CompCert also compiles each module to assembly, from which
# tools/baremetal/stack-bound.sh computes the bound of every function with the list of the
# functions that take the call depth that native-verified writes, and the glue, compiled with
# LX_STACK_MARK, reports the stack that each call of a module function used: a case fails when a
# call used more than its function's bound (docs/native-bare-metal.md, test 3), and a module whose
# stack the tool cannot bound does not build.  The script prints, for each module, the cases that
# pass, that fail, and that do not run because the translation lacks their export, the largest
# high-water mark, and the largest stack of a call with its bound, then each failure, the modules
# without a translation, and the modules that CompCert cannot compile or link, with the first
# lines of the error.  It fails unless every case that runs passes
# and every translated module builds.  CCOMP and CCOMP_STDLIB are as for tools/baremetal/build.sh,
# and QEMU names qemu-system-aarch64.  Build the modules' targets first, as tests/verified/run.sh
# requires.
# Usage: tests/baremetal/verified.sh [--module NAME]
set -euo pipefail
only=""
if [ "$#" -ne 0 ]; then
  if [ "$#" -ne 2 ] || [ "$1" != "--module" ] || [ -z "$2" ]; then
    echo "usage: tests/baremetal/verified.sh [--module NAME]" >&2
    exit 2
  fi
  only=$2
fi
ccomp=${CCOMP:-ccomp}
stdlib=()
if [ -n "${CCOMP_STDLIB:-}" ]; then
  stdlib=(-stdlib "$CCOMP_STDLIB")
fi
qemu=${QEMU:-qemu-system-aarch64}
jobs=${JOBS:-4}
export STACK_SIZE=${STACK_SIZE:-0x400000}
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$root/build/baremetal/verified
cd "$root"
tools/leanrun --timeout 30m lake --log-level error build native-verified Verified.Examples.Cases
rm -rf "$out"
mkdir -p "$out"

"$ccomp" "${stdlib[@]}" -I tools/baremetal/libc -I tools -Dmain=host_main -c tools/native-host.c \
  -o "$out/host.o"
"$ccomp" "${stdlib[@]}" -I tools/baremetal/libc -c tools/baremetal/libc/libc.c -o "$out/libc.o"

modules=0
untranslated=""
unbuilt=()
while IFS=: read -r module constant name; do
  if [ -n "$only" ] && [ "$name" != "$only" ]; then
    continue
  fi
  modules=$((modules + 1))
  status=0
  tools/leanrun --timeout 10m lake env .lake/build/bin/native-verified emit "$module" "$constant" \
    "$name" "$out" </dev/null || status=$?
  if [ "$status" -eq 3 ]; then
    untranslated="$untranslated $name"
    continue
  elif [ "$status" -ne 0 ]; then
    exit "$status"
  fi
  b=$out/$name.bm
  mkdir -p "$b"
  if ! { "$ccomp" "${stdlib[@]}" -fno-common -c "$out/$name.c" -o "$b/module.o" &&
      "$ccomp" "${stdlib[@]}" -fno-common -S "$out/$name.c" -o "$b/module.s" &&
      tools/baremetal/stack-bound.sh "$out/$name.depth" "$b/module.s" >"$b/bounds.txt" &&
      "$ccomp" "${stdlib[@]}" -I tools -DLX_STACK_MARK -c "$out/${name}_glue.c" -o "$b/glue.o" &&
      tools/baremetal/build.sh "$b/host.elf" "$out/host.o" "$out/libc.o" "$b/glue.o" \
        "$b/module.o"; } >"$b/build.err" 2>&1; then
    unbuilt+=("$name: $(head -n 3 "$b/build.err" | paste -sd' ')")
    rm -f "$out/$name.exports"
  fi
done <"$root/tests/verified/modules.txt"
if [ "$modules" -eq 0 ]; then
  echo "fail: unknown module $only" >&2
  exit 2
fi

cases=$out/cases.txt
if ! tools/leanrun --timeout 10m lake env lean --run Verified/Examples/Cases.lean \
    >"$cases" 2>"$out/cases.err"; then
  cat "$out/cases.err" >&2
  echo "fail: native Lean exited with an error" >&2
  exit 1
fi
awk -F'|' '
  BEGIN { OFS = FS }
  NR == FNR { targets[$1 FS $2] = $3 FS $4; next }
  { print; key = $1 FS $2 }
  key in targets {
    split(targets[key], target, FS)
    $1 = target[1]; $2 = target[2]; print
  }' "$root/tests/verified/library-cases.txt" "$cases" >"$cases.library"
mv "$cases.library" "$cases"
tools/leanrun --timeout 30m lake --log-level error build Demos.Euler.Cases Examples.Shape.Cases
modcases=$out/module-cases.txt
if ! tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Native/ModuleCases.lean \
    >"$modcases" 2>"$out/module-cases.err"; then
  cat "$out/module-cases.err" >&2
  echo "fail: native Lean exited with an error" >&2
  exit 1
fi

# The work list: one line per case that runs, its kind (V for tests/verified, M for a module
# case) first, and the counts of the cases that do not run.
declare -A omitted
: >"$out/work.txt"
while IFS='|' read -r name export rest; do
  if [ -n "$only" ] && [ "$name" != "$only" ]; then
    continue
  fi
  [ -f "$out/$name.exports" ] || continue
  if grep -qxF "$export" "$out/$name.exports"; then
    printf 'V|%s|%s|%s\n' "$name" "$export" "$rest" >>"$out/work.txt"
  else
    omitted[$name]=$((${omitted[$name]:-0} + 1))
  fi
done <"$cases"
while IFS='|' read -r module name rest; do
  case "$module" in
    euler) prog=euler ;;
    shapes) prog=sums ;;
    *) continue ;;
  esac
  if [ -n "$only" ] && [ "$prog" != "$only" ]; then
    continue
  fi
  [ -f "$out/$prog.exports" ] || continue
  if grep -qxF "$name" "$out/$prog.exports"; then
    printf 'M|%s|%s|%s\n' "$prog" "$name" "$rest" >>"$out/work.txt"
  else
    omitted[$prog]=$((${omitted[$prog]:-0} + 1))
  fi
done <"$modcases"

# Runs the host of module $1 with the arguments that follow, in the directory $w, and leaves
# its standard output and error in $w/stdout.txt and $w/stderr.txt, its exit status in $code,
# its stack high-water mark in $stack, and any report of an exception in $exception.
run_host() {
  local elf=$out/$1.bm/host.elf
  shift
  {
    printf '%s\0' "$(($# + 1))" host
    for a in "$@"; do
      printf '%s\0' "$a"
    done
  } >"$w/args.bin"
  rm -f "$w/serial.txt"
  code=0
  timeout 300 "$qemu" -M virt -cpu cortex-a57 -m 1G -display none -monitor none \
    -serial "file:$w/serial.txt" -semihosting-config enable=on,target=native \
    -device "loader,file=$w/args.bin,addr=0x7F000000,force-raw=on" -kernel "$elf" \
    </dev/null || code=$?
  grep -v '^E:\|^R:' "$w/serial.txt" >"$w/stdout.txt" || true
  sed -n 's/^E://p' "$w/serial.txt" >"$w/stderr.txt"
  stack=$(sed -n 's/^R:exit .* stack \([0-9]*\)$/\1/p' "$w/serial.txt")
  sed -n 's/^R:call \([^ ]*\) stack \([0-9]*\)$/\1 \2/p' "$w/serial.txt" >"$w/calls.txt"
  exception=$(grep '^R:exception\|^R:level' "$w/serial.txt" || true)
}

# Runs the work lines of shard $1 and writes one result line per case to $out/results.$1: the
# module, pass or fail, the high-water mark, and for a failure its description.
run_shard() {
  w=$out/shard.$1
  mkdir -p "$w"
  local res=$out/results.$1
  : >"$res"
  local kind name export result args expected live allocsMax got held allocs frees message
  while IFS='|' read -r kind name export result args expected live allocsMax; do
    read -ra argv <<<"$args"
    message=""
    if [ "$kind" = "M" ]; then
      run_host "$name" call "$export" "$result" "${argv[@]}"
      got=$(tr -d '[] ' <"$w/stdout.txt" | paste -sd, -)
      if [ "$code" -ne 0 ] || [ "$got" != "$expected" ]; then
        message="$export $args: $got (status $code) $(paste -sd' ' "$w/stderr.txt"), expected $expected"
      fi
    elif [ "$expected" = "trap" ]; then
      run_host "$name" call "$export" "$result" "${argv[@]}"
      if [ "$code" -eq 0 ]; then
        message="$export $args: returned, expected a trap at unreachable"
      elif ! grep -q 'wasm `unreachable` instruction executed' "$w/stderr.txt"; then
        message="$export $args: $(paste -sd' ' "$w/stderr.txt") (status $code), expected a trap at unreachable"
      fi
    else
      allocs=""
      if [ -z "$live" ]; then
        run_host "$name" call "$export" "$result" "${argv[@]}"
        got=$(paste -sd' ' "$w/stdout.txt")
        held=""
      else
        run_host "$name" call-stats "$export" "$result" "${argv[@]}"
        got=$(sed '$d' "$w/stdout.txt" | paste -sd' ')
        read -r _ allocs frees < <(tail -n 1 "$w/stdout.txt") || true
        held=$((${allocs:-0} - ${frees:-0}))
      fi
      if [ "$code" -ne 0 ]; then
        message="$export $args: $(paste -sd' ' "$w/stderr.txt") (status $code), expected $expected"
      elif [ -n "$allocsMax" ] && [ "$allocs" -gt "$allocsMax" ]; then
        message="$export $args: $allocs allocations, at most $allocsMax expected"
      elif [ "$got" != "$expected" ] || [ "$held" != "$live" ]; then
        message="$export $args: $got, expected $expected; live blocks $held, expected $live"
      fi
    fi
    check=$(awk 'NR == FNR { b[$2] = $1; next }
      {
        u = $2 + 0
        if (!($1 in b)) print "bad " $1 " used " u " bytes of stack without a bound"
        else if (u > b[$1] + 0) print "bad " $1 " used " u " bytes of stack, above its bound " b[$1]
        if (u >= used) { used = u; bound = ($1 in b) ? b[$1] : 0 }
      }
      END { print "max " used + 0, bound + 0 }' "$out/$name.bm/bounds.txt" "$w/calls.txt")
    read -r _ used ubound < <(grep '^max ' <<<"$check")
    bad=$(sed -n 's/^bad //p' <<<"$check" | paste -sd';' -)
    if [ -z "$message" ] && [ -n "$bad" ]; then
      message="$export $args: $bad"
    fi
    if [ -n "$exception" ]; then
      message="$export $args: $exception"
    elif [ -n "$stack" ] && [ "$stack" -ge "$((STACK_SIZE))" ]; then
      message="$export $args: the stack's high-water mark reached its size"
    fi
    if [ -z "$message" ]; then
      printf '%s|pass|%s|%s|%s|\n' "$name" "${stack:-0}" "$used" "$ubound" >>"$res"
    else
      printf '%s|fail|%s|%s|%s|%s\n' "$name" "${stack:-0}" "$used" "$ubound" "$message" >>"$res"
    fi
  done < <(awk -v k="$1" -v n="$jobs" '(NR - 1) % n == k' "$out/work.txt")
}

start=$(date +%s)
for ((k = 0; k < jobs; k++)); do
  run_shard "$k" &
done
wait
seconds=$(($(date +%s) - start))

cat "$out"/results.* >"$out/results.txt"
for name in "${!omitted[@]}"; do
  printf '%s|omitted|%s\n' "$name" "${omitted[$name]}" >>"$out/results.txt"
done
awk -F'|' '
  $2 == "pass" { pass[$1]++; seen[$1] = 1 }
  $2 == "fail" { fail[$1]++; seen[$1] = 1 }
  $2 == "pass" || $2 == "fail" {
    if ($3 + 0 > stack[$1]) stack[$1] = $3 + 0
    if ($4 + 0 >= used[$1]) { used[$1] = $4 + 0; bound[$1] = $5 + 0 }
  }
  $2 == "omitted" { omit[$1] += $3; seen[$1] = 1 }
  END {
    for (m in seen) {
      printf "baremetal verified: %s passed %d failed %d not run %d stack %d module %d bound %d\n",
        m, pass[m], fail[m], omit[m], stack[m], used[m], bound[m]
      tp += pass[m]; tf += fail[m]; to += omit[m]
    }
    printf "baremetal verified: total passed %d failed %d not run %d\n", tp, tf, to > "/dev/stderr"
  }' "$out/results.txt" 2>"$out/total.txt" | sort
cat "$out/total.txt"
echo "baremetal verified: $(wc -l <"$out/work.txt") cases in $seconds s with $jobs jobs"
awk -F'|' '$2 == "fail" { print "fail: " $1 " " $6 }' "$out/results.txt"
echo "baremetal verified: modules without a translation:${untranslated:- none}"
if [ "${#unbuilt[@]}" -eq 0 ]; then
  echo "baremetal verified: modules that do not build: none"
else
  for u in "${unbuilt[@]}"; do
    echo "baremetal verified: module that does not build: $u"
  done
fi
failed=$(awk -F'|' '$2 == "fail"' "$out/results.txt" | wc -l)
passed=$(awk -F'|' '$2 == "pass"' "$out/results.txt" | wc -l)
[ "$passed" -gt 0 ] && [ "$failed" -eq 0 ] && [ "${#unbuilt[@]}" -eq 0 ]
