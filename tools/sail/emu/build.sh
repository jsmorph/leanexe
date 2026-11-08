#!/bin/sh
# Usage: build.sh MODEL_DIR OUT_DIR
# Builds OUT_DIR/fpemu, the harness fpemu.c linked with Sail's C translation of the
# floating-point functions of the arm-v9.4-a model (MODEL_DIR is sail-arm's arm-v9.4-a
# directory).  Sail checks the files that
# ../translate.sh names, in its order, runs the REPL commands of ../fp-slice.isail with the C
# target's rewrites in place of the Lean ones, and writes OUT_DIR/armv9fp.c and armv9fp.h with
# ":target c".  gcc compiles them with fpemu.c and the C files of Sail's library that the
# emulator calls, against GMP.  Sail reads and writes the results of its Z3 calls in
# OUT_DIR/sail_smt_cache, which starts as a copy of MODEL_DIR's cache, so that a run beside
# translate.sh does not write the same file.  GNU time prints each step's elapsed seconds and
# peak memory.
set -eu
model=$1
out=$2
mkdir -p "$out"
out="$(CDPATH= cd -- "$out" && pwd)"
here="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
script=$(sed 's/^:rewrites lean$/:rewrites c/' "$here/../fp-slice.isail")
case $script in
  *":rewrites c"*) ;;
  *) echo "build.sh: fp-slice.isail has no line :rewrites lean" >&2; exit 1 ;;
esac
if [ -f "$model/sail_smt_cache" ] && [ ! -f "$out/sail_smt_cache" ]; then
  cp "$model/sail_smt_cache" "$out/sail_smt_cache"
fi
lib="$(sail --dir)/lib"
cd "$model"
srcs="src/prelude.sail src/decode_start.sail src/builtins.sail src/v8_base.sail src/stubs.sail
  src/interrupts.sail src/interface.sail src/devices.sail src/impdefs.sail src/mem.sail
  src/decode_end.sail src/fetch.sail src/termination_measures.sail $here/../fp-measures.sail"
# shellcheck disable=SC2086
{ printf '%s\n' "$script"; echo ":target c, $out/armv9fp"; } |
  /usr/bin/time -f "generation: %e s, %M KiB" \
    sail -dprofile -no_warn -no_color -memo_z3 -memo_z3_path "$out/sail_smt_cache" \
      -just_check -interact_custom -c --c-no-main $srcs
/usr/bin/time -f "build: %e s, %M KiB" \
  gcc -O2 -I "$lib" -I "$out" -o "$out/fpemu" "$here/fpemu.c" "$out/armv9fp.c" \
    "$lib/sail.c" "$lib/rts.c" "$lib/elf.c" "$lib/sail_failure.c" -lgmp
