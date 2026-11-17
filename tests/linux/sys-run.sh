#!/bin/sh
# Tests the descriptions of the Linux call layer on an AArch64 Linux host.  The script checks
# LeanExe/Linux/CallTable.lean and tests/linux/sys/frame.c against the pinned syzlang files with
# tools/linux-calls.py --check, and the table against the independent lowering of
# tests/linux/syzlang-lowering.py, and requires each check to reject seeded faults: altered copies
# of the generated files, a description outside the table, an altered syzlang file, and altered
# tables.  It builds the frame test with "$CC -O1 -static" and runs it natively and under
# qemu-aarch64, QEMU's user-mode emulator, with the option --qemu, which skips with their reasons
# the steps that QEMU 8.2.2 does not run as Linux does; each run must exit with status 0.  It then
# builds the frame test of each seeded fault that tools/linux-calls.py --frame-faults writes and
# requires the status that the generator predicts, natively and under qemu-aarch64, except under
# qemu-aarch64 for a fault whose first altered step QEMU skips.  Each run of a frame test takes
# place in a new empty directory, within TIMEOUT seconds, 120 unless set, in a scope of one core and
# 2G of memory.  CC names the C compiler, cc unless set, and QEMU_USER the emulator, qemu-aarch64
# unless set.  The products lie in build/linux/sys.
# Usage: tests/linux/sys-run.sh [SYZLANG_DIR]
#
# SYZLANG_DIR holds sys.txt, sys.txt.const, and LICENSE of syzkaller commit
# a3e64cfc0d091fba81397847a5ab9790a4a944ca; the default is tests/linux/syzlang.
set -eu
set -f
if [ "$#" -gt 1 ]; then
  printf 'Usage: %s [SYZLANG_DIR]\n' "$0" >&2
  exit 2
fi
fail() {
  printf 'linux calls %s: %s\n' "$1" "$2" >&2
  exit 1
}
[ "$(uname -s) $(uname -m)" = "Linux aarch64" ] || fail "host" "not an AArch64 Linux host"
cc=${CC:-cc}
qemu=${QEMU_USER:-qemu-aarch64}
for tool in uv "$cc" "$qemu" systemd-run; do
  command -v "$tool" > /dev/null 2>&1 || fail "tools" "$tool is not on the search path"
done

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
syz=${1:-$root/tests/linux/syzlang}
syz=$(CDPATH= cd -- "$syz" && pwd)
cd "$root"
out="$root/build/linux/sys"
rm -rf "$out"
mkdir -p "$out"

uv run python -I tools/linux-calls.py --check "$syz" > "$out/descriptions.txt" ||
  fail "descriptions" "$(cat "$out/descriptions.txt")"
uv run python -I tests/linux/syzlang-lowering.py "$syz" > "$out/lowering.txt" ||
  fail "independent lowering" "$(cat "$out/lowering.txt")"

# Seeded faults of the two checks.  The generator's check runs in a copy of the generated files'
# directories, and alter NAME FILE EXPRESSION changes FILE of the copy with the sed EXPRESSION,
# requires the check to fail, and restores FILE.  lowering NAME EXPRESSION requires the independent
# lowering to reject the table changed with the sed EXPRESSION.
copy="$out/generator"
mkdir -p "$copy/LeanExe" "$copy/tests/linux"
cp -R LeanExe/Linux "$copy/LeanExe/Linux"
cp -R tests/linux/sys "$copy/tests/linux/sys"
rejected=0
alter() {
  cp "$copy/$2" "$copy/$2.saved"
  sed -i "$3" "$copy/$2"
  cmp -s "$copy/$2" "$copy/$2.saved" && fail "seeded fault $1" "the expression changed nothing"
  if (cd "$copy" && uv run python -I "$root/tools/linux-calls.py" --check "$syz" \
      > "$out/fault-$1.txt" 2>&1); then
    fail "seeded fault $1" "the generator's check passed"
  fi
  mv "$copy/$2.saved" "$copy/$2"
  rejected=$((rejected + 1))
}
lowering() {
  sed "$2" LeanExe/Linux/CallTable.lean > "$out/lowering-$1.lean"
  cmp -s LeanExe/Linux/CallTable.lean "$out/lowering-$1.lean" &&
    fail "seeded fault $1" "the expression changed nothing"
  if uv run python -I tests/linux/syzlang-lowering.py "$syz" "$out/lowering-$1.lean" \
      > "$out/fault-$1.txt" 2>&1; then
    fail "seeded fault $1" "the independent lowering accepted the altered table"
  fi
  rejected=$((rejected + 1))
}
(cd "$copy" && uv run python -I "$root/tools/linux-calls.py" --check "$syz" \
  > "$out/fault-none.txt" 2>&1) || fail "seeded faults" "the unaltered copy fails the check"
alter record LeanExe/Linux/CallTable.lean '0,/\.record 16/s//.record 8/'
alter number LeanExe/Linux/CallTable.lean '0,/56, 257/s//56, 258/'
alter fills tests/linux/sys/frame.c '0,/\.fills = 16/s//.fills = 15/'
alter stray LeanExe/Linux/Replies.lean \
  '$a def strayCall : Call := ⟨"close", 57, 3, [.fd], false, false⟩'
mkdir -p "$out/syzlang"
cp "$syz/sys.txt" "$syz/sys.txt.const" "$syz/LICENSE" "$out/syzlang/"
printf '# An added line.\n' >> "$out/syzlang/sys.txt"
if uv run python -I tools/linux-calls.py --check "$out/syzlang" > "$out/fault-digest.txt" 2>&1
then
  fail "seeded fault digest" "the generator accepted an altered sys.txt"
fi
rejected=$((rejected + 1))
lowering kind '0,/\.record 16/s//.record 8/'
lowering amd64 '0,/56, 257/s//56, 258/'
lowering opens '0,/\.value\], true, false⟩/s//.value], false, false⟩/'
lowering layout '0,/⟨"mode", 8, 8⟩/s//⟨"mode", 4, 8⟩/'
lowering lines '0,/lines 886 to 889/s//lines 885 to 889/'
lowering region '0,/\[(x1, x2\.toNat)\] := /s//[(x1, x3.toNat)] := /'
printf 'linux call seeded faults detected: %s\n' "$rejected"

# Runs the command given as arguments in a scope of one core and 2G of memory.
scoped() {
  systemd-run --user --scope -q -p CPUQuota=100% -p MemoryMax=2G timeout "${TIMEOUT:-120}" "$@"
}
# frame NAME EXPECTED COMMAND...: runs COMMAND in the new empty directory $out/run-NAME, with its
# output in $out/NAME.out, and requires the exit status EXPECTED.
cases=0
frame() {
  run=$1
  want=$2
  shift 2
  rm -rf "$out/run-$run"
  mkdir "$out/run-$run"
  status=0
  (cd "$out/run-$run" && scoped "$@" > "$out/$run.out" 2>&1 < /dev/null) || status=$?
  [ "$status" -eq "$want" ] ||
    fail "frame test $run" "status $status, expected $want: $(tail -n 3 "$out/$run.out")"
  cases=$((cases + 1))
}
"$cc" -O1 -static -o "$out/frame" tests/linux/sys/frame.c > "$out/frame-build.txt" 2>&1 ||
  fail "frame test" "$(cat "$out/frame-build.txt")"
frame native 0 "$out/frame"
frame qemu 0 "$qemu" "$out/frame" --qemu
tail -n 1 "$out/native.out"
grep '^skip: ' "$out/qemu.out" | sed 's/^/qemu-aarch64: /'
tail -n 1 "$out/qemu.out"

faults="$out/frame-faults"
uv run python -I tools/linux-calls.py --frame-faults "$faults" "$syz" > "$out/frame-faults.txt"
native=0
emulated=0
while read -r name expected where; do
  "$cc" -O1 -static -o "$faults/$name" "$faults/$name.c" > "$faults/$name-build.txt" 2>&1 ||
    fail "frame fault $name" "$(cat "$faults/$name-build.txt")"
  frame "fault-$name-native" "$expected" "$faults/$name"
  native=$((native + 1))
  if [ "$where" = native ]; then
    printf 'qemu-aarch64: frame fault %s not run: QEMU skips the step that it reaches first\n' \
      "$name"
  else
    frame "fault-$name-qemu" "$expected" "$qemu" "$faults/$name" --qemu
    emulated=$((emulated + 1))
  fi
done < "$out/frame-faults.txt"
[ "$native" -gt 0 ] || fail "frame faults" "the generator wrote none"
printf 'linux frame seeded faults detected: %s natively, %s under qemu-aarch64\n' "$native" \
  "$emulated"
printf 'linux frame cases passed: %s\n' "$cases"
