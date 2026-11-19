#!/bin/sh
# Checks the manifest checker of Demos/ManifestCheck.  It checks the hashes of the reviewed
# specification and samples against spec.sha256, builds the demo's modules, elaborates
# tests/manifest-check/Axioms.lean, which restates the call theorems of the pure core and the
# theorems of the WASI command and fails on an axiom other than propext, Classical.choice, and
# Quot.sound, and emits and validates the command's module.
#
# It then runs the command in the Wasmtime host with a test directory preopened, and compares each
# output line with the verdict of GNU `sha256sum -c` on the same manifest in the same directory,
# whose "FAILED open or read" counts as FAILED.  The directory holds a short file, an empty file, a
# file whose name has spaces, a file of 5 MiB and 17 bytes that takes 81 reads, a file whose bytes
# differ from its manifest's digest, a symbolic link to a file in the directory, and a symbolic link
# to a file outside it.  A manifest of files that match, with a name through `sub/..`, a binary-mode
# line, and a line without a final newline, must give `NAME: OK` for each line and status 0.  A
# manifest that adds the changed file, a missing file, a name with `..` that leaves the directory,
# an absolute name, and the link that leaves it must give status 1 and the verdicts of
# `sha256sum -c`, except that each name that leaves the directory, which `sha256sum -c` reads and
# finds OK, must give FAILED: the host refuses to open it.  A manifest with a line that is not in
# the format and an empty manifest must write nothing and give status 1, as `sha256sum -c --strict`
# does, and so must a run with no argument and a run with two.  A missing manifest must give status
# 44 (`noent`), a manifest named outside the directory status 63 (`perm`), and a run whose
# standard output is /dev/full status 51 (`nospc`), the errno of the write that failed.  No run may
# write to stderr.
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

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
out="$root/build/manifest-check"
host="$root/build/tools/leanexe-wasmtime-host"
module="$out/command.wasm"
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

sha256sum --quiet -c Demos/ManifestCheck/spec.sha256 ||
  fail spec "Spec.lean or Samples.lean differs from the reviewed version"

tools/leanrun --timeout 90m --log "$out/build.log" lake build Demos.ManifestCheck.Compiled \
  Demos.ManifestCheck.CommandStart
tools/leanrun --timeout 10m lake env lean tests/manifest-check/Axioms.lean
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Demos.ManifestCheck.Command \
  Demos.ManifestCheck.command.module "$module"
wasm-tools validate "$module"
printf 'command.wasm: %s bytes\n' "$(wc -c < "$module" | tr -d ' ')"

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

digest() {
  sha256sum "$1" | cut -d ' ' -f 1
}

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

# run OUT ARG...: runs the module with the program name `check` and the arguments ARG, the test
# directory preopened, and returns its status.
run() {
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

# checked NAME STATUS MANIFEST: the run on MANIFEST exits with STATUS, writes the verdicts of
# `expected MANIFEST`, and writes nothing to stderr, and `sha256sum -c` exits with the same status.
checked() {
  name=$1
  want=$2
  manifest=$3
  stdout="$out/$name.stdout"
  expected "$manifest" > "$out/$name.expected" ||
    fail "$name" "sha256sum -c does not find each name outside the directory OK"
  gnu=0
  (cd "$dir" && sha256sum -c "$manifest" > /dev/null 2>&1) || gnu=$?
  [ "$gnu" -eq "$want" ] || fail "$name" "sha256sum -c status $gnu, expected $want"
  status=0
  run "$stdout" "$manifest" || status=$?
  [ "$status" -eq "$want" ] || fail "$name" "status $status, expected $want"
  cmp -s "$stdout" "$out/$name.expected" ||
    fail "$name" "the verdicts differ from those of sha256sum -c"
  [ ! -s "$stdout.stderr" ] || fail "$name" "output on stderr"
  cases=$((cases + 1))
  verdicts=$((verdicts + $(wc -l < "$stdout")))
}

# silent NAME STATUS ARG...: the run exits with STATUS and writes nothing to stdout or stderr.
silent() {
  name=$1
  want=$2
  shift 2
  stdout="$out/$name.stdout"
  status=0
  run "$stdout" "$@" || status=$?
  [ "$status" -eq "$want" ] || fail "$name" "status $status, expected $want"
  [ ! -s "$stdout" ] || fail "$name" "output where none is expected"
  [ ! -s "$stdout.stderr" ] || fail "$name" "output on stderr"
  cases=$((cases + 1))
}

checked good 0 good.sha256
checked mixed 1 mixed.sha256
[ "$(grep -c ': OK$' "$out/good.stdout")" -eq 6 ] || fail good "not every line says OK"
for manifest in malformed.sha256 empty.sha256; do
  gnu=0
  (cd "$dir" && sha256sum -c --strict "$manifest" > /dev/null 2>&1) || gnu=$?
  [ "$gnu" -eq 1 ] || fail "$manifest" "sha256sum -c --strict status $gnu, expected 1"
done
silent malformed 1 malformed.sha256
silent empty-manifest 1 empty.sha256
silent no-argument 1
silent two-arguments 1 good.sha256 mixed.sha256
silent missing-manifest 44 absent.sha256
silent outside-manifest 63 ../outside/manifest.sha256

err="$out/full.stderr"
status=0
timeout 600s "$host" --dir "$dir" --arg check --arg good.sha256 --stdout-file /dev/full \
  run "$module" 2> "$err" || status=$?
[ "$status" -eq 51 ] || fail full "status $status, expected 51"
[ ! -s "$err" ] || fail full "output on stderr"
cases=$((cases + 1))

printf 'manifest check: %s runs passed, %s verdicts agree with sha256sum -c\n' "$cases" "$verdicts"
