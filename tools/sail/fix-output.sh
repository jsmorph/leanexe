#!/bin/sh
# Usage: fix-output.sh DIR LIB
# Edits the Lean output of Sail 0.20.3 (root module DIR/LIB.lean, modules in DIR/LIB) so that it
# elaborates.  Each edit keeps the meaning of the definitions:
#  - Real.lean, written by --lean-real-numbers, opens a namespace Defs that no output declares,
#    and Lean rejects the open.  The script deletes the line.
#  - Lean v4.34 parses `assert` at the start of a do element as its own assert element, so a call
#    of the model's assert there fails; the script qualifies the 119 calls as LIB.assert.
#  - IncrementInstructionCounter compares two single-bit vectors built by BitVec.join1, whose
#    types BitVec [a].length and BitVec [b].length Lean unifies by reducing a and b; with b a
#    let-bound sum, the reduction does not finish (tested for 90 s on v4.29.0 and v4.34.0-rc2).
#    The script compares the two bits, since BitVec.join1 [x] is x for a bit x.
#  - FPRoundBase__1 compares errors with the real 0.5, which Sail prints as `f e 1/2`, an
#    application divided by 2; the script writes (1/2).
set -eu
dir=$1
lib=$2
if [ -f "$dir/$lib/Real.lean" ]; then
  sed -i '/^open Defs$/d' "$dir/$lib/Real.lean"
fi
sed -i "s/\\bassert /$lib.assert /g" "$dir/$lib.lean"
perl -0pi -e 's/\(\(BitVec\.join1 \[\(integer_access old_value 64\)\]\) != \(BitVec\.join1 \[\(integer_access\s+new_value 64\)\]\)\)/((integer_access old_value 64) != (integer_access new_value 64))/' "$dir/$lib.lean"
sed -i 's| 1/2)| (1/2))|g' "$dir/$lib.lean"
if grep -q 'BitVec.join1 \[(integer_access old_value 64)\]' "$dir/$lib.lean"; then
  echo "fix-output.sh: the comparison in IncrementInstructionCounter was not found" >&2
  exit 1
fi
