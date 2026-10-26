#!/bin/sh
set -eu
set -f
export PATH="$PATH:$HOME/.local/bin:$HOME/.cargo/bin"

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"
fixtures="$root/tests/wasi/acceptance"
out="$root/build/wasi/acceptance"
host="$root/build/tools/leanexe-wasmtime-host"
mkdir -p "$out"

if [ ! -x "$host" ]; then
  printf 'Missing native host: %s\n' "$host" >&2
  exit 1
fi
if [ "$root/tools/wasmtime-host.c" -nt "$host" ]; then
  printf 'Native host is older than tools/wasmtime-host.c; rebuild it with tools/build-wasmtime-host.sh\n' >&2
  exit 1
fi

tools/leanrun --timeout 10m --log build/wasi/acceptance/build.log lake build \
  Verified.Examples.WasiDepth Verified.Examples.WasiRetainTotal
tools/leanrun --timeout 5m lake env lean tests/wasi/AcceptanceAxioms.lean
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiDepth \
  Verified.Examples.WasiDepth.compiled.module "$out/depth.wasm"
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean Verified.Examples.WasiRetain \
  Verified.Examples.WasiRetain.compiled.module "$out/retain.wasm"
wasm-tools validate "$out/depth.wasm"
wasm-tools validate "$out/retain.wasm"

case_count=0

compare_file() {
  if ! cmp "$1" "$2"; then
    printf '%s: expected %s, observed %s\n' "$case_name" "$1" "$2" >&2
    cat "$host_stderr" >&2
    exit 1
  fi
}

begin_case() {
  case_dir="$out/$case_name"
  mkdir -p "$case_dir"
  guest_stdout="$case_dir/guest.stdout"
  guest_stderr="$case_dir/guest.stderr"
  host_stdout="$case_dir/host.stdout"
  host_stderr="$case_dir/host.stderr"
  control="$case_dir/control"
  : >"$guest_stdout"
  : >"$guest_stderr"
  : >"$control"
}

tab=$(printf '\t')
while IFS="$tab" read -r case_name module export_name argument kind input result allocations releases stdout status; do
  begin_case
  if [ "$argument" = _ ]; then set --; else set -- "i64:$argument"; fi
  if [ "$result" = error ] || [ "$result" = trap ]; then
    operation=call
    printf '%s\n' "$result" >"$case_dir/expected.control"
  else
    operation=call-stats
    if [ "$result" = _ ]; then result=; fi
    printf '%s\nstats %s %s\n' "$result" "$allocations" "$releases" >"$case_dir/expected.control"
  fi
  case $status in
    ''|*[!0-9]*)
      printf '%s: expected status is not a decimal number: %s\n' "$case_name" "$status" >&2
      exit 1 ;;
  esac
  observed=0
  timeout 30s "$host" --wasi --stdin-file "$fixtures/$input" \
    --stdout-file "$guest_stdout" --stderr-file "$guest_stderr" --control-file "$control" \
    "$operation" "$out/$module.wasm" "$export_name" "$kind" "$@" \
    >"$host_stdout" 2>"$host_stderr" || observed=$?
  if [ "$observed" -ne "$status" ]; then
    printf '%s: expected process status %s, observed %s\n' "$case_name" "$status" "$observed" >&2
    cat "$host_stderr" >&2
    printf 'Captures: %s\n' "$case_dir" >&2
    exit 1
  fi
  compare_file "$case_dir/expected.control" "$control"
  compare_file "$fixtures/$stdout" "$guest_stdout"
  compare_file "$fixtures/empty.bin" "$guest_stderr"
  compare_file "$fixtures/empty.bin" "$host_stdout"
  if [ "$result" = trap ]; then
    case "$(cat "$host_stderr")" in
      *unreachable*) ;;
      *)
        printf '%s: expected an unreachable diagnostic in %s\n' "$case_name" "$host_stderr" >&2
        exit 1 ;;
    esac
  elif [ "$result" = error ]; then
    if [ ! -s "$host_stderr" ]; then
      printf '%s: expected a host error diagnostic in %s\n' "$case_name" "$host_stderr" >&2
      exit 1
    fi
  else
    compare_file "$fixtures/empty.bin" "$host_stderr"
  fi
  case_count=$((case_count + 1))
done <"$fixtures/cases.tsv"

session_fixtures="$root/tests/wasi/return-session"
case_name=returned-root-session
begin_case
observed=0
timeout 30s "$host" --wasi --stdin-file "$session_fixtures/input.bin" \
  --stdout-file "$guest_stdout" --stderr-file "$guest_stderr" --control-file "$control" \
  session "$out/retain.wasm" <"$session_fixtures/session.txt" \
  >"$host_stdout" 2>"$host_stderr" || observed=$?
if [ "$observed" -ne 0 ]; then
  printf '%s: expected process status 0, observed %s\n' "$case_name" "$observed" >&2
  cat "$host_stderr" >&2
  printf 'Captures: %s\n' "$case_dir" >&2
  exit 1
fi
compare_file "$session_fixtures/control.txt" "$control"
compare_file "$session_fixtures/stdout.bin" "$guest_stdout"
compare_file "$session_fixtures/empty.bin" "$guest_stderr"
compare_file "$session_fixtures/empty.bin" "$host_stdout"
compare_file "$session_fixtures/empty.bin" "$host_stderr"
case_count=$((case_count + 1))

printf 'WASI depth and retained-resource tests passed: %s native cases\n' "$case_count"
