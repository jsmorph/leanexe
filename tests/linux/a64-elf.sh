#!/usr/bin/env bash
# The Linux executables of the AArch64 back end on an AArch64 Linux host: the flip of bit 5 of
# each byte of tests/TestSupport/A64/FlipElf.lean, which reads standard input to its end and
# writes the flipped bytes to standard output.  a64-elf emit writes flip.elf and, for each case,
# the message and the bytes that standard output must receive.  Lean then elaborates
# tests/TestSupport/A64/ImageFilesFlipElf.lean in the directory of those files, so that the kernel
# checks that flip.elf holds the bytes that its generator gives and proves its theorems, each with
# no axiom beyond propext, Classical.choice, and Quot.sound.  The script runs the executable on the
# host's processor and under qemu-aarch64, QEMU's user-mode emulator, each run within TIMEOUT
# seconds, 120 unless set, in a scope of one core and 2G of memory.  Each case runs from a file and
# from a pipe into which the script writes the message in pieces of 1, 3, 5, and 7 bytes, each
# after a pause of PAUSE seconds, 0.2 unless set, and then the rest.  A message of at most
# 8,800,000 bytes must give the flipped message and status 0, and a longer one status 64 and no
# output.  On the host's processor, runs outside the theorems exercise the error paths: standard
# input closed or a directory gives status 65 and no output, standard output closed or /dev/full
# status 66, and a file size limit with SIGXFSZ ignored a short write and then EFBIG, so status
# 66 after a prefix of the output.  A reader that closes standard output early ends the process
# with SIGPIPE, status 141, which the theorems leave out.
#
# a64-elf emit also writes stamp.elf, the stamp program of tests/TestSupport/A64/StampElf.lean
# around the same function, which reads the file stamp.in, runs the function on the realtime
# clock's 16 bytes, 16 random bytes, and the file's bytes, and writes the result to stamp.out.
# Lean elaborates tests/TestSupport/A64/ImageFilesStampElf.lean in the same way.  Each run of
# stamp.elf takes place in a directory of its own under OUT/stamp.  Inputs of at most 8,799,968
# bytes, from a file with a longer stamp.out beforehand and from a FIFO fed in pieces, natively
# and under qemu-aarch64, must give status 0 and a stamp.out whose bytes, with bit 5 flipped, are
# a clock reading within a second of the run, 16 bytes, and the input.  An input of 8,799,969
# bytes must give status 64 with stamp.out unchanged, a missing stamp.in status 67, stamp.in a
# directory status 68, and a directory without write permission status 70.  Runs under umask 0
# check the mode 0644, a run with standard input closed checks a descriptor of 0, and three runs
# on one input must differ at each random byte.  On the host's processor, a file size limit gives
# status 74 after a prefix, and the executable run as stamp.out status 70 from ETXTBSY, which
# QEMU 8.2.2 does not return.  The products lie in OUT, build/linux/a64-elf unless set.
# Usage: tests/linux/a64-elf.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root"
out=$(realpath -m "${OUT:-$root/build/linux/a64-elf}")
qemu=${QEMU_USER:-/usr/bin/qemu-aarch64}
rm -rf "${out:?}"
mkdir -p "$out"
tools/leanrun --timeout 60m --memory-high "${MEM:-8G}" lake --log-level error build a64-elf \
  TestSupport.A64.FlipElf TestSupport.A64.StampElf LeanExe.A64.File LeanExe.A64.Proof.StampImage
status=0
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-elf emit "$out" || status=1
chmod +x "$out/flip.elf" "$out/stamp.elf"
# Elaborates the module $1 of tests/TestSupport/A64 in the directory of the files and requires $2
# lines of axioms, each a subset of the standard three.
kernel_check() {
  if tools/leanrun --timeout 60m --memory-high 8G lake env sh -c 'cd "$1" && lean "$2"' sh "$out" \
      "$root/tests/TestSupport/A64/$1.lean" >"$out/$1.check" 2>&1 &&
      [ "$(grep -c "depends on axioms\|does not depend on any axioms" "$out/$1.check")" = "$2" ] &&
      ! grep "depends on axioms" "$out/$1.check" |
        sed 's/.*depends on axioms: \[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' |
        grep -qvx 'propext\|Classical.choice\|Quot.sound'; then
    echo "pass: the kernel's check of $1.lean"
  else
    echo "fail: the kernel's check of $1.lean: $(head -c 600 "$out/$1.check")"
    status=1
  fi
}
kernel_check ImageFilesFlipElf 6
kernel_check ImageFilesStampElf 4
# Runs the command given as arguments in a scope of one core and 2G of memory.
scoped() {
  systemd-run --user --scope -q -p CPUQuota=100% -p MemoryMax=2G timeout "${TIMEOUT:-120}" "$@"
}
# Writes the bytes of the file $1 in pieces of 1, 3, 5, and 7 bytes, each after a pause, and then
# the rest.
pieces() {
  local n off=0 size
  size=$(stat -c %s "$1")
  for n in 1 3 5 7; do
    [ "$off" -lt "$size" ] || return 0
    sleep "${PAUSE:-0.2}"
    dd if="$1" bs=1 skip="$off" count="$n" status=none
    off=$((off + n))
  done
  [ "$off" -lt "$size" ] || return 0
  sleep "${PAUSE:-0.2}"
  tail -c +"$((off + 1))" "$1"
}
# Checks the run named $1 that ended with status $2 and wrote the file $3 against the status $4
# and the file $5.
check() {
  if [ "$2" -eq "$4" ] && cmp -s "$5" "$3"; then
    echo "pass: $1: status $2, $(stat -c %s "$3") bytes"
  else
    echo "fail: $1: status $2 where $4 is due, output $(head -c 32 "$3" | od -An -tx1)"
    status=1
  fi
}
: >"$out/empty"
# Runs the case whose message is $1 and whose output must be $2 with status $3, natively and
# under qemu-aarch64, from a file and from a pipe.
run_case() {
  local in=$1 want=$2 st=$3 name code
  name=$(basename "${in%.in}")
  for how in native qemu; do
    if [ "$how" = native ]; then set -- "$out/flip.elf"; else set -- "$qemu" "$out/flip.elf"; fi
    code=0
    scoped "$@" <"$in" >"$out/$name.$how.file" || code=$?
    check "$name $how from a file" "$code" "$out/$name.$how.file" "$st" "$want"
    code=0
    pieces "$in" | scoped "$@" >"$out/$name.$how.pipe" || code=$?
    check "$name $how from a pipe in pieces" "$code" "$out/$name.$how.pipe" "$st" "$want"
  done
}
for n in $(ls "$out" | sed -n 's/^flip-\([0-9]*\)\.in$/\1/p' | sort -n); do
  run_case "$out/flip-$n.in" "$out/flip-$n.want" 0
done
for in in "$out"/flipover-*.in; do
  run_case "$in" "$out/empty" 64
done
# The error paths, on the host's processor.
code=0
scoped "$out/flip.elf" <&- >"$out/closed-in.out" || code=$?
check "standard input closed" "$code" "$out/closed-in.out" 65 "$out/empty"
code=0
scoped "$out/flip.elf" <"$out" >"$out/dir-in.out" || code=$?
check "standard input a directory" "$code" "$out/dir-in.out" 65 "$out/empty"
code=0
scoped "$out/flip.elf" <"$out/flip-4096.in" >&- || code=$?
check "standard output closed" "$code" "$out/empty" 66 "$out/empty"
code=0
scoped "$out/flip.elf" <"$out/flip-4096.in" >/dev/full || code=$?
check "standard output /dev/full" "$code" "$out/empty" 66 "$out/empty"
code=0
(trap '' XFSZ; ulimit -f 64; exec "$out/flip.elf" <"$out/flip-1000000.in" >"$out/limit.out") ||
  code=$?
head -c "$(stat -c %s "$out/limit.out")" "$out/flip-1000000.want" >"$out/limit.want"
if [ "$(stat -c %s "$out/limit.out")" -lt 1000000 ]; then
  check "a file size limit of 64 blocks" "$code" "$out/limit.out" 66 "$out/limit.want"
else
  echo "fail: a file size limit of 64 blocks: the whole output was written"
  status=1
fi
code=0
set +o pipefail
scoped "$out/flip.elf" <"$out/flip-8800000.in" | head -c 100 >"$out/early.out"
code=${PIPESTATUS[0]}
set -o pipefail
if [ "$code" -eq 141 ]; then
  echo "pass: a reader that closes early: status 141, SIGPIPE"
else
  echo "fail: a reader that closes early: status $code"
  status=1
fi
# The stamp executable.  Each run takes place in its own directory under $out/stamp, whose files
# stamp.in and stamp.out the executable opens.
stamp=$out/stamp.elf
head -c 8799968 "$out/flip-8800000.in" >"$out/stamp-8799968.in"
head -c 8799968 "$out/flip-8800000.want" >"$out/stamp-8799968.want"
head -c 8799969 "$out/flipover-8800001.in" >"$out/stampover-8799969.in"
# Creates the directory $out/stamp/$1 and prints its path.
stamp_dir() {
  mkdir -p "$out/stamp/$1"
  echo "$out/stamp/$1"
}
# Runs the stamp executable in the directory $2, on the host's processor when $1 is native and
# under qemu-aarch64 otherwise, with standard input from /dev/null, and prints its status.
stamp_exec() {
  local code=0
  if [ "$1" = native ]; then
    (cd "$2" && scoped "$stamp" </dev/null >/dev/null) || code=$?
  else
    (cd "$2" && scoped "$qemu" "$stamp" </dev/null >/dev/null) || code=$?
  fi
  echo "$code"
}
# Prints the word of the 8 bytes from byte $2 of the file $1, each with bit 5 flipped, the first
# byte lowest.
flipped_word() {
  local -a bs
  local i v=0
  read -ra bs < <(od -An -tu1 -v -j "$2" -N 8 "$1")
  for ((i = 7; i >= 0; i--)); do v=$(((v << 8) | (bs[i] ^ 32))); done
  echo "$v"
}
# Checks the run named $1 that ended with status $2 and wrote the file $3 between the seconds $4
# and $5 against the file $6, the input with bit 5 of each byte flipped: status 0, then the
# flipped clock's seconds within a second of the run and its nanoseconds below 10^9, 16 more
# bytes, and the bytes of $6.
stamp_check() {
  local sec nsec
  if [ "$2" -eq 0 ] && [ -f "$3" ] && [ "$(stat -c %s "$3")" -eq $(($(stat -c %s "$6") + 32)) ] &&
      tail -c +33 "$3" | cmp -s - "$6"; then
    sec=$(flipped_word "$3" 0)
    nsec=$(flipped_word "$3" 8)
    if [ "$sec" -ge $(($4 - 1)) ] && [ "$sec" -le $(($5 + 1)) ] && [ "$nsec" -ge 0 ] &&
        [ "$nsec" -lt 1000000000 ]; then
      echo "pass: $1: status 0, $(stat -c %s "$3") bytes"
    else
      echo "fail: $1: the clock reads $sec s and $nsec ns, and the run took the seconds $4 to $5"
      status=1
    fi
  else
    echo "fail: $1: status $2, output $(head -c 48 "$3" 2>/dev/null | od -An -tx1)"
    status=1
  fi
}
# Checks the run named $1 that ended with status $2 against the status $3, and that the directory
# $4 holds no stamp.out, or holds the file $5 as stamp.out when $5 is given.
stamp_fail() {
  local kept
  if [ -n "${5:-}" ]; then
    cmp -s "$5" "$4/stamp.out" && kept=yes || kept=no
  else
    [ ! -e "$4/stamp.out" ] && kept=yes || kept=no
  fi
  if [ "$2" -eq "$3" ] && [ "$kept" = yes ]; then
    echo "pass: $1: status $2"
  else
    echo "fail: $1: status $2 where $3 is due, stamp.out as due: $kept"
    status=1
  fi
}
# Runs the case whose input is the file $1 and whose flipped input is the file $2, on the host's
# processor and under qemu-aarch64: with stamp.in a copy of $1 and a stamp.out 4,096 bytes longer
# than the output, which O_TRUNC must cut, and with stamp.in a FIFO into which the script writes
# $1 in pieces.
stamp_case() {
  local name d code t0 t1 writer
  name=$(basename "${1%.in}")
  for how in native qemu; do
    d=$(stamp_dir "$name.$how.file")
    cp "$1" "$d/stamp.in"
    head -c $(($(stat -c %s "$1") + 32 + 4096)) /dev/zero >"$d/stamp.out"
    t0=$(date +%s)
    code=$(stamp_exec "$how" "$d")
    t1=$(date +%s)
    stamp_check "stamp $name $how from a file" "$code" "$d/stamp.out" "$t0" "$t1" "$2"
    d=$(stamp_dir "$name.$how.fifo")
    mkfifo "$d/stamp.in"
    pieces "$1" >"$d/stamp.in" &
    writer=$!
    t0=$(date +%s)
    code=$(stamp_exec "$how" "$d")
    t1=$(date +%s)
    kill "$writer" 2>/dev/null || true
    wait "$writer" 2>/dev/null || true
    stamp_check "stamp $name $how from a FIFO in pieces" "$code" "$d/stamp.out" "$t0" "$t1" "$2"
  done
}
for n in 0 1 4095 4096 65536 1000000; do
  stamp_case "$out/flip-$n.in" "$out/flip-$n.want"
done
stamp_case "$out/stamp-8799968.in" "$out/stamp-8799968.want"
for how in native qemu; do
  d=$(stamp_dir "over.$how")
  cp "$out/stampover-8799969.in" "$d/stamp.in"
  head -c 100 /dev/zero >"$d/before"
  cp "$d/before" "$d/stamp.out"
  stamp_fail "stamp of 8,799,969 bytes $how" "$(stamp_exec "$how" "$d")" 64 "$d" "$d/before"
  d=$(stamp_dir "missing.$how")
  stamp_fail "stamp without stamp.in $how" "$(stamp_exec "$how" "$d")" 67 "$d"
  d=$(stamp_dir "dir.$how")
  mkdir "$d/stamp.in"
  stamp_fail "stamp with stamp.in a directory $how" "$(stamp_exec "$how" "$d")" 68 "$d"
  d=$(stamp_dir "readonly.$how")
  cp "$out/flip-1.in" "$d/stamp.in"
  chmod a-w "$d"
  code=$(stamp_exec "$how" "$d")
  chmod u+w "$d"
  stamp_fail "stamp in a directory without write permission $how" "$code" 70 "$d"
  d=$(stamp_dir "umask.$how")
  cp "$out/flip-4096.in" "$d/stamp.in"
  t0=$(date +%s)
  code=$(umask 0 && stamp_exec "$how" "$d")
  t1=$(date +%s)
  stamp_check "stamp under umask 0 $how" "$code" "$d/stamp.out" "$t0" "$t1" "$out/flip-4096.want"
  if [ "$(stat -c %a "$d/stamp.out" 2>/dev/null)" = 644 ]; then
    echo "pass: stamp under umask 0 $how: mode 644"
  else
    echo "fail: stamp under umask 0 $how: mode $(stat -c %a "$d/stamp.out" 2>/dev/null)"
    status=1
  fi
done
# With standard input closed, the first openat returns descriptor 0.
d=$(stamp_dir closed-in)
cp "$out/flip-4096.in" "$d/stamp.in"
t0=$(date +%s)
code=0
(cd "$d" && scoped "$stamp" <&-) || code=$?
t1=$(date +%s)
stamp_check "stamp with standard input closed" "$code" "$d/stamp.out" "$t0" "$t1" \
  "$out/flip-4096.want"
# Three runs on one input must differ at each of the 16 random bytes.
for i in 1 2 3; do
  d=$(stamp_dir "random.$i")
  cp "$out/flip-1.in" "$d/stamp.in"
  code=$(stamp_exec native "$d")
  [ "$code" -eq 0 ] || { echo "fail: stamp's random run $i: status $code"; status=1; }
done
read -ra r1 < <(od -An -tu1 -v -j 16 -N 16 "$out/stamp/random.1/stamp.out")
read -ra r2 < <(od -An -tu1 -v -j 16 -N 16 "$out/stamp/random.2/stamp.out")
read -ra r3 < <(od -An -tu1 -v -j 16 -N 16 "$out/stamp/random.3/stamp.out")
same=0
for ((i = 0; i < 16; i++)); do
  if [ "${r1[i]:-x}" = "${r2[i]:-y}" ] && [ "${r2[i]:-y}" = "${r3[i]:-z}" ]; then
    same=$((same + 1))
  fi
done
if [ "${#r1[@]}" -eq 16 ] && [ "$same" -eq 0 ]; then
  echo "pass: stamp's random bytes differ among three runs at each of 16 positions"
else
  echo "fail: stamp's random bytes agree among three runs at $same positions"
  status=1
fi
# A file size limit of 64 blocks with SIGXFSZ ignored gives a short write and then EFBIG.
d=$(stamp_dir limit)
cp "$out/flip-1000000.in" "$d/stamp.in"
code=0
(trap '' XFSZ; ulimit -f 64; cd "$d" && exec "$stamp" </dev/null) || code=$?
size=$(stat -c %s "$d/stamp.out")
if [ "$code" -eq 74 ] && [ "$size" -gt 32 ] && [ "$size" -lt 1000032 ] &&
    tail -c +33 "$d/stamp.out" | cmp -s - <(head -c $((size - 32)) "$out/flip-1000000.want"); then
  echo "pass: stamp with a file size limit of 64 blocks: status 74, $size bytes"
else
  echo "fail: stamp with a file size limit of 64 blocks: status $code, $size bytes"
  status=1
fi
# Linux refuses, with ETXTBSY, to open for writing the executable that a process runs.
d=$(stamp_dir txtbsy)
cp "$out/flip-1.in" "$d/stamp.in"
cp "$stamp" "$d/stamp.out"
code=0
(cd "$d" && scoped ./stamp.out </dev/null) || code=$?
stamp_fail "stamp running as stamp.out" "$code" 70 "$d" "$stamp"
echo "skip: stamp running as stamp.out under qemu-aarch64: QEMU 8.2.2 opens it for writing"
exit "$status"
