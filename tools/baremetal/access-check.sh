#!/usr/bin/env bash
# Fails when an AArch64 assembly file has an instruction whose access must be aligned in RAM as
# the startup code maps it, Normal memory with SCTLR_EL1.A clear, and prints each such line with
# its file and line number.  There an unaligned load or store of single or multiple registers is
# performed (Arm Architecture Reference Manual, DDI 0487 issue M.d, section B2.8.2.1.1, page
# B2-312), but the Load-Exclusive, Store-Exclusive, Load-Acquire, Store-Release, and atomic
# instructions, SETG*, and the memory copy and set instructions keep alignment rules, and the
# 64-byte single-copy atomic and Read-Check-Write instructions always require alignment.
# Usage: tools/baremetal/access-check.sh FILE.s...
set -euo pipefail
if [ "$#" -eq 0 ]; then
  echo "usage: tools/baremetal/access-check.sh FILE.s..." >&2
  exit 2
fi
classes='ld(a)?x[rp]|st(l)?x[rp]|ldar|ldapr|ldapur|ldlar|stlr|stllr|stlur|swp|cas'
classes+='|ld(add|clr|eor|set|smax|smin|umax|umin)|st(add|clr|eor|set|smax|smin|umax|umin)'
classes+='|setg|set[pme]|cpy|ld64b|st64b|rcw'
if grep -n -i -E "^[[:space:]]*($classes)[a-z0-9]*[[:space:]]" "$@"; then
  echo "tools/baremetal/access-check.sh: the instructions above require aligned accesses" >&2
  exit 1
fi
