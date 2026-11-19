#!/bin/sh
# Checks the manifest checker of Demos/ManifestCheck.  It checks the hashes of the reviewed
# specification and samples against spec.sha256, builds the demo's modules, elaborates
# tests/manifest-check/Axioms.lean, which restates the call theorems of the pure core and the
# theorems of the WASI command and fails on an axiom other than propext, Classical.choice, and
# Quot.sound, and emits and validates the command's module.  It writes the module's AArch64 Linux
# executable with `a64-wasi wasm`, which fails when genWasiElf rejects the module, and prints the
# executable's size and SHA-256.
#
# It then runs the command with each runner of RUNNERS, by default `wasm native qemu`: the module in
# the Wasmtime host with a test directory preopened, the executable on the host's processor, which
# must be AArch64 Linux, with the directory open as descriptor 3, and the executable in the same way
# under qemu-aarch64, QEMU's user-mode emulator, or QEMU_USER when set, which must be QEMU 9.2 or
# later, the first release that implements `openat2`.  A runner is a function `run_RUNNER OUT
# ARG...` that runs the command with the arguments ARG after the program name, writes its stdout to
# OUT and its stderr to OUT.stderr, and returns the command's status.  Each run's output lines must
# be the verdicts of GNU `sha256sum -c` on the same manifest in the same directory, whose "FAILED
# open or read" counts as FAILED.  The directory holds a short file, an empty file, a file whose
# name has spaces, a file of 5 MiB and 17 bytes that takes 82 reads, a file whose bytes differ from
# its manifest's digest, a symbolic link to a file in the directory, and a symbolic link to a file
# outside it.  A manifest of files that match, with a name through `sub/..`, a binary-mode line, and
# a line without a final newline, must give `NAME: OK` for each line and status 0.  A manifest that
# adds the changed file, a missing file, a name with `..` that leaves the directory, an absolute
# name, and the link that leaves it must give status 1 and the verdicts of `sha256sum -c`, except
# that each name that leaves the directory, which `sha256sum -c` reads and finds OK, must give
# FAILED: the host refuses to open it.  A manifest with a line that is not in the format and an
# empty manifest must write nothing and give status 1, as `sha256sum -c --strict` does, and so must
# a run with no argument and a run with two.  A missing manifest must give status 44 (`noent`), a
# manifest named outside the directory status 63 (`perm`), and a run whose standard output is
# /dev/full status 51 (`nospc`), the errno of the write that failed.  No run may write to stderr.
#
# When RUNNERS holds `native`, the executable then runs on the manifests of files that match and of
# mixed verdicts under strace, and each run must write the same verdicts.  The trace may hold no
# call but `openat`, `openat2`, `read`, `statx`, `close`, `write`, and `exit_group`.  The one
# `openat` is the startup's check that descriptor 3 is a directory, which opens `.` relative to it
# with O_DIRECTORY and closes the result.  Every `openat2` must name descriptor 3, the flags
# O_RDONLY and O_CLOEXEC, and the resolution flags RESOLVE_BENEATH and RESOLVE_NO_MAGICLINKS, every
# `statx` an empty path with AT_EMPTY_PATH and the mask STATX_ALL (0xfff), and every `write`
# descriptor 1.  Every `read`, `statx`, and `close` must name the descriptor that the last `openat`
# or `openat2` returned, which a `close` must end before the next open and before the exit.  The
# `openat2` of each name that leaves the directory, through `..`, as an absolute name, or through
# the link, must fail in the kernel with EXDEV.
#
# Five native runs on the manifest of files that match replace results with strace's injection.  When
# the third `read`, the first of a.txt, fails with EIO, a.txt must give FAILED and the other lines
# OK, with status 1.  When the first three `openat2` calls fail with EAGAIN, the fourth opens the
# manifest, and the run must write the verdicts of the run without injection, with status 0.  When
# the first four fail with EAGAIN, the run must stop after them with status 29 (`io`), the shim's
# errno for EAGAIN, and write nothing.  When the manifest's `close`, the first `close` after the
# startup's, fails with EIO, the run must write nothing and exit with status 29 (`io`).  When every
# `write` returns 0, the run must make 11 writes of a.txt's line of 10 bytes, each offering the
# whole line, and exit with status 77 without output.  The file theorems of the executable are
# checked in tests/linux/a64-wasi.sh, which writes the executable from the same module with the same
# commands.
#
# The pure module's samples run in `tests/verified/run.sh --cases manifestCheck`.
# Usage: tests/manifest-check/run.sh
set -eu
set -f
for tool in wasm-tools sha256sum; do
  if ! command -v "$tool" > /dev/null 2>&1; then
    printf '%s is not on the search path\n' "$tool" >&2
    exit 1
  fi
done
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
      fi
      version=$("$qemu" --version | sed -n '1s/.* version \([0-9]*\)\.\([0-9]*\).*/\1 \2/p')
      set -- $version
      if [ "$#" -ne 2 ] || [ "$1" -lt 9 ] || { [ "$1" -eq 9 ] && [ "$2" -lt 2 ]; }; then
        printf '%s is not QEMU 9.2 or later, which implements openat2\n' "$qemu" >&2
        exit 1
      fi ;;
  esac
done

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
out="$root/build/manifest-check"
host="$root/build/tools/leanexe-wasmtime-host"
module="$out/command.wasm"
elf="$out/command.elf"
dir="$out/dir"
mkdir -p "$out"

if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi

fail() {
  printf 'manifest check %s: %s\n' "$1" "$2" >&2
  exit 1
}

digest() {
  sha256sum "$1" | cut -d ' ' -f 1
}

sha256sum --quiet -c Demos/ManifestCheck/spec.sha256 ||
  fail spec "Spec.lean or Samples.lean differs from the reviewed version"

tools/leanrun --timeout 90m --log "$out/build.log" lake build Demos.ManifestCheck.Compiled \
  Demos.ManifestCheck.CommandStart a64-wasi
tools/leanrun --timeout 10m lake env lean tests/manifest-check/Axioms.lean
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Demos.ManifestCheck.Command \
  Demos.ManifestCheck.command.module "$module"
wasm-tools validate "$module"
printf 'command.wasm: %s bytes\n' "$(wc -c < "$module" | tr -d ' ')"
tools/leanrun --timeout 10m lake env .lake/build/bin/a64-wasi wasm "$module" "$elf" ||
  fail elf "genWasiElf rejects the module"
chmod +x "$elf"
printf 'command.elf: %s bytes, SHA-256 %s\n' "$(wc -c < "$elf" | tr -d ' ')" "$(digest "$elf")"

# The test directory and a directory beside it that the runs must not reach.
set +f
rm -rf "$dir" "$out/outside"
set -f
mkdir -p "$dir/sub" "$out/outside"
printf 'hello\n' > "$dir/a.txt"
: > "$dir/empty"
printf 'abc' > "$dir/name with spaces"
head -c 5242897 /dev/urandom > "$dir/big.bin"
printf 'original\n' > "$dir/changed.txt"
printf 'secret\n' > "$out/outside/secret.txt"
ln -s a.txt "$dir/inside-link"
ln -s ../outside/secret.txt "$dir/outside-link"

a=$(digest "$dir/a.txt")
empty=$(digest "$dir/empty")
spaces=$(digest "$dir/name with spaces")
big=$(digest "$dir/big.bin")
changed=$(digest "$dir/changed.txt")
secret=$(digest "$out/outside/secret.txt")
printf 'originaL\n' > "$dir/changed.txt"

printf '%s  a.txt\n%s  empty\n%s  name with spaces\n%s *big.bin\n%s  sub/../a.txt\n%s  inside-link' \
  "$a" "$empty" "$spaces" "$big" "$a" "$a" > "$dir/good.sha256"
{
  printf '%s  a.txt\n' "$a"
  printf '%s  changed.txt\n' "$changed"
  printf '%s  missing.txt\n' "$a"
  printf '%s  ../outside/secret.txt\n' "$secret"
  printf '%s  %s\n' "$secret" "$out/outside/secret.txt"
  printf '%s  outside-link\n' "$secret"
  printf '%s  big.bin\n' "$big"
} > "$dir/mixed.sha256"
printf '%s  a.txt\n%s a.txt\n' "$a" "$a" > "$dir/malformed.sha256"
: > "$dir/empty.sha256"
cp "$dir/good.sha256" "$out/outside/manifest.sha256"

cases=0
verdicts=0

# run_wasm OUT ARG...: runs the module in the Wasmtime host with the program name `check` and the
# arguments ARG, the test directory preopened.
run_wasm() {
  stdout=$1
  shift
  set -- check "$@"
  count=$#
  for value in "$@"; do
    set -- "$@" --arg "$value"
  done
  shift "$count"
  timeout 600s "$host" --dir "$dir" "$@" --stdout-file "$stdout" run "$module" 2> "$stdout.stderr"
}

# run_native OUT ARG...: runs the executable on the host's processor with the arguments ARG and the
# test directory open as descriptor 3.
run_native() {
  stdout=$1
  shift
  timeout 600s "$elf" "$@" > "$stdout" 2> "$stdout.stderr" 3< "$dir"
}

# run_qemu OUT ARG...: runs the executable under QEMU's user-mode emulator with the arguments ARG
# and the test directory open as descriptor 3.
run_qemu() {
  stdout=$1
  shift
  timeout 600s "$qemu" "$elf" "$@" > "$stdout" 2> "$stdout.stderr" 3< "$dir"
}

# expected MANIFEST: the verdicts of `sha256sum -c` on MANIFEST in the test directory, with FAILED
# for each name that leaves the directory, which `sha256sum -c` must find OK.
expected() {
  (cd "$dir" && sha256sum -c "$1" 2> /dev/null) | sed 's/: FAILED open or read$/: FAILED/' |
    awk -v outside="$out/outside/secret.txt" '
      { name = $0; sub(/: (OK|FAILED)$/, "", name) }
      name ~ /^\.\.\// || name == outside || name == "outside-link" {
        if ($0 !~ /: OK$/) bad = 1
        print name ": FAILED"
        next
      }
      { print }
      END { exit bad }'
}

# The verdicts that the runs must write, and the statuses of `sha256sum -c`.
for name in good mixed; do
  expected "$name.sha256" > "$out/$name.expected" ||
    fail "$name" "sha256sum -c does not find each name outside the directory OK"
done
for check in "good 0" "mixed 1"; do
  set -- $check
  gnu=0
  (cd "$dir" && sha256sum -c "$1.sha256" > /dev/null 2>&1) || gnu=$?
  [ "$gnu" -eq "$2" ] || fail "$1" "sha256sum -c status $gnu, expected $2"
done
[ "$(grep -c ': OK$' "$out/good.expected")" -eq 6 ] || fail good "not every line says OK"
for manifest in malformed.sha256 empty.sha256; do
  gnu=0
  (cd "$dir" && sha256sum -c --strict "$manifest" > /dev/null 2>&1) || gnu=$?
  [ "$gnu" -eq 1 ] || fail "$manifest" "sha256sum -c --strict status $gnu, expected 1"
done

# checked RUNNER NAME STATUS: the run on NAME.sha256 exits with STATUS, writes the verdicts of
# `expected NAME.sha256`, and writes nothing to stderr.
checked() {
  runner=$1
  name=$2
  want=$3
  stdout="$out/$runner-$name.stdout"
  status=0
  "run_$runner" "$stdout" "$name.sha256" || status=$?
  [ "$status" -eq "$want" ] || fail "$runner $name" "status $status, expected $want"
  cmp -s "$stdout" "$out/$name.expected" ||
    fail "$runner $name" "the verdicts differ from those of sha256sum -c"
  [ ! -s "$stdout.stderr" ] || fail "$runner $name" "output on stderr"
  cases=$((cases + 1))
  verdicts=$((verdicts + $(wc -l < "$stdout")))
}

# silent RUNNER NAME STATUS ARG...: the run exits with STATUS and writes nothing to stdout or
# stderr.
silent() {
  runner=$1
  name=$2
  want=$3
  shift 3
  stdout="$out/$runner-$name.stdout"
  status=0
  "run_$runner" "$stdout" "$@" || status=$?
  [ "$status" -eq "$want" ] || fail "$runner $name" "status $status, expected $want"
  [ ! -s "$stdout" ] || fail "$runner $name" "output where none is expected"
  [ ! -s "$stdout.stderr" ] || fail "$runner $name" "output on stderr"
  cases=$((cases + 1))
}

# full RUNNER: the run on the manifest of files that match with standard output /dev/full exits
# with status 51 and writes nothing to stderr.
full() {
  runner=$1
  err="$out/$runner-full.stderr"
  status=0
  case $runner in
    wasm)
      timeout 600s "$host" --dir "$dir" --arg check --arg good.sha256 --stdout-file /dev/full \
        run "$module" 2> "$err" || status=$? ;;
    native) timeout 600s "$elf" good.sha256 > /dev/full 2> "$err" 3< "$dir" || status=$? ;;
    qemu)
      timeout 600s "$qemu" "$elf" good.sha256 > /dev/full 2> "$err" 3< "$dir" || status=$? ;;
  esac
  [ "$status" -eq 51 ] || fail "$runner full" "status $status, expected 51"
  [ ! -s "$err" ] || fail "$runner full" "output on stderr"
  cases=$((cases + 1))
}

for runner in $RUNNERS; do
  checked "$runner" good 0
  checked "$runner" mixed 1
  silent "$runner" malformed 1 malformed.sha256
  silent "$runner" empty-manifest 1 empty.sha256
  silent "$runner" no-argument 1
  silent "$runner" two-arguments 1 good.sha256 mixed.sha256
  silent "$runner" missing-manifest 44 absent.sha256
  silent "$runner" outside-manifest 63 ../outside/manifest.sha256
  full "$runner"
done

# traced NAME STATUS: the run on NAME.sha256 under strace exits with STATUS, writes the verdicts of
# `expected NAME.sha256`, and makes only the calls that the header describes.  The calls after the
# execve are left in $out/native-NAME.calls.
traced() {
  name=$1
  want=$2
  trace="$out/native-$name.strace"
  body="$out/native-$name.calls"
  stdout="$out/native-$name-strace.stdout"
  status=0
  strace -s 4096 -o "$trace" "$elf" "$name.sha256" > "$stdout" 3< "$dir" || status=$?
  [ "$status" -eq "$want" ] || fail "strace $name" "status $status, expected $want"
  cmp -s "$stdout" "$out/$name.expected" ||
    fail "strace $name" "the verdicts differ from those of sha256sum -c"
  sed -n '/^execve(/,$p' "$trace" | tail -n +2 | sed '/^+++/d' > "$body"
  bad=$(grep -v '^\(openat\|openat2\|read\|statx\|close\|write\|exit_group\)(' "$body" | head -1)
  [ -z "$bad" ] || fail "strace $name" "the call $bad"
  [ "$(grep -c '^openat(' "$body")" -eq 1 ] &&
    grep -q '^openat(3, "\.", O_RDONLY|O_\(CLOEXEC|O_DIRECTORY\|DIRECTORY|O_CLOEXEC\)) = [0-9]' \
      "$body" || fail "strace $name" "the startup's openat"
  bad=$(grep '^openat2(' "$body" |
    grep -v '^openat2(3, "[^"]*", {flags=O_RDONLY|O_CLOEXEC, resolve=[A-Z_|]*}, 24) = ' |
    head -1)
  [ -z "$bad" ] || fail "strace $name" "the call $bad"
  bad=$(grep '^openat2(' "$body" | grep -v 'resolve=[A-Z_|]*RESOLVE_BENEATH' | head -1)
  [ -z "$bad" ] || fail "strace $name" "the call $bad"
  bad=$(grep '^openat2(' "$body" | grep -v 'resolve=[A-Z_|]*RESOLVE_NO_MAGICLINKS' | head -1)
  [ -z "$bad" ] || fail "strace $name" "the call $bad"
  bad=$(grep '^statx(' "$body" |
    grep -v '^statx([0-9]*, "", AT_STATX_SYNC_AS_STAT|AT_EMPTY_PATH, STATX_ALL, ' | head -1)
  [ -z "$bad" ] || fail "strace $name" "the call $bad"
  bad=$(awk '
    function bad(line) { print line; failed = 1; exit }
    /^openat2?\(/ {
      if (held != "") bad($0)
      if ($0 ~ /\) += [0-9]+$/) held = $NF
      next
    }
    /^(read|statx|close)\(/ {
      fd = $0
      sub(/^[a-z]+\(/, "", fd)
      sub(/[,)].*/, "", fd)
      if (fd != held) bad($0)
      if ($0 ~ /^close\(/) held = ""
    }
    END { if (!failed && held != "") print "descriptor " held " left open" }' "$body")
  [ -z "$bad" ] || fail "strace $name" "the use of descriptors at $bad"
  bad=$(grep '^write(' "$body" | grep -v '^write(1, ' | head -1)
  [ -z "$bad" ] || fail "strace $name" "the call $bad"
  cases=$((cases + 1))
}

# injected NAME STATUS EXPECTED INJECTION: the run on good.sha256 under strace with the injection
# INJECTION exits with STATUS, writes the bytes of the file EXPECTED, and writes nothing to stderr.
# Its trace is left in $out/native-NAME.strace.
injected() {
  name=$1
  want=$2
  expect=$3
  trace="$out/native-$name.strace"
  stdout="$out/native-$name.stdout"
  status=0
  strace -o "$trace" -e "inject=$4" "$elf" good.sha256 > "$stdout" 2> "$stdout.stderr" 3< "$dir" ||
    status=$?
  [ "$status" -eq "$want" ] || fail "strace $name" "status $status, expected $want"
  cmp -s "$stdout" "$expect" || fail "strace $name" "the output differs from $expect"
  [ ! -s "$stdout.stderr" ] || fail "strace $name" "output on stderr"
  cases=$((cases + 1))
}

case " $RUNNERS " in
  *" native "*)
    traced good 0
    traced mixed 1
    for leaving in ../outside/secret.txt "$out/outside/secret.txt" outside-link; do
      grep -q "^openat2(3, \"$leaving\", .* = -1 EXDEV " "$out/native-mixed.calls" ||
        fail "strace mixed" "the openat2 of $leaving does not fail with EXDEV"
    done
    sed '1s/: OK$/: FAILED/' "$out/good.expected" > "$out/read-failed.expected"
    : > "$out/nothing.expected"
    injected read-failed 1 "$out/read-failed.expected" read:error=EIO:when=3
    injected again-3 0 "$out/good.expected" openat2:error=EAGAIN:when=1..3
    [ "$(grep -c '^openat2(3, "good.sha256", .* = -1 EAGAIN ' "$out/native-again-3.strace")" \
      -eq 3 ] || fail "strace again-3" "the manifest's opens are not three EAGAIN and a descriptor"
    injected again-4 29 "$out/nothing.expected" openat2:error=EAGAIN:when=1..4
    [ "$(grep -c '^openat2(' "$out/native-again-4.strace")" -eq 4 ] ||
      fail "strace again-4" "the run does not stop after four openat2 calls"
    injected close-failed 29 "$out/nothing.expected" close:error=EIO:when=2
    injected stalled 77 "$out/nothing.expected" write:retval=0
    [ "$(grep -c '^write(' "$out/native-stalled.strace")" -eq 11 ] &&
      [ "$(grep -c '^write(1, "a.txt: OK\\n", 10) *= 0 ' "$out/native-stalled.strace")" -eq 11 ] ||
      fail "strace stalled" "the writes are not 11 offers of a.txt's line" ;;
esac

printf 'manifest check: %s runs passed, %s verdicts agree with sha256sum -c\n' "$cases" "$verdicts"
