#!/bin/sh
# Usage: translate.sh MODEL_DIR OUT_DIR NAME SCRIPT [SAIL_OPTIONS_AND_FILES]
# Translates the slice of the arm-v9.4-a model (MODEL_DIR is sail-arm's arm-v9.4-a directory)
# that the REPL script SCRIPT selects into the Lake project OUT_DIR/NAME with Sail's Lean back
# end.  The commands of SCRIPT and ":target lean, NAME" run through -interact_custom, which skips
# the interpreter's rewrites that -is applies before a script.  The files are the model's files
# up to mem.sail in the Makefile's order, decode_end.sail, fetch.sail (which defines
# ThisInstrLength, declared in v8_base.sail), and termination_measures.sail.  Sail checks
# definitions in order, so v8_base.sail's functions call only functions declared in the files
# before it or in it.  A function declared there and defined in an omitted file would appear in
# the Lean output without a definition, and Lean reports no such identifier for this slice.
# The whole model does not fit in 7 GiB.  The Lean output imports ArmExtras.lean for the model's
# external functions.
set -eu
model=$1
out=$2
name=$3
script=$4
shift 4
mkdir -p "$out"
extras="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)/ArmExtras.lean"
cd "$model"
srcs="src/prelude.sail src/decode_start.sail src/builtins.sail src/v8_base.sail src/stubs.sail
  src/interrupts.sail src/interface.sail src/devices.sail src/impdefs.sail src/mem.sail
  src/decode_end.sail src/fetch.sail src/termination_measures.sail"
# shellcheck disable=SC2086
{ cat "$script"; echo ":target lean, $name"; } |
  sail -dprofile -no_warn -no_color -memo_z3 -undefined_gen -just_check -interact_custom \
    --lean --lean-output-dir "$out" --lean-force-output --lean-line-width 100 \
    --lean-import-file "$extras" $srcs "$@"
