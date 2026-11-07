#!/usr/bin/env bash
# Checks the instructions of an ARMv7-M image that require a word-aligned address even when
# CCR.UNALIGN_TRP is 0, the setting of the startup code: LDRD, STRD, LDM, STM, PUSH, POP, LDREX,
# STREX, LDC, STC, VLDR, VSTR, VLDM, VSTM, VPUSH, and VPOP (Armv7-M Architecture Reference Manual,
# DDI 0403E.e, section A3.2.1, page A3-65), whose unaligned access takes a UsageFault.  DISASM is
# the output of objdump -d for the image, the startup code, its reports, and the run-time
# functions included.  An instruction is safe when its base register is sp and its offset a
# multiple of 4, since an ARMv7-M implementation treats bits [1:0] of sp as RAZ/WI (section
# B1.4.1, page B1-516), or when it reads a literal at a pc-relative address that objdump gives
# and that is a multiple of 4.  The script prints the number of instructions of each kind and
# fails when another instruction of the class remains, printing it with its function.
# Usage: tools/baremetal/armv7m/access-check.sh DISASM
set -euo pipefail
if [ "$#" -ne 1 ]; then
  echo "usage: tools/baremetal/armv7m/access-check.sh DISASM" >&2
  exit 2
fi
awk '
function hexval(s,   v, i, c) {
  v = 0
  for (i = 1; i <= length(s); i++) {
    c = index("0123456789abcdef", substr(s, i, 1))
    if (c == 0) return -1
    v = v * 16 + c - 1
  }
  return v
}
BEGIN {
  cond = "(eq|ne|cs|hs|cc|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le|al)?"
  class = "^(ldrd|strd|ldm(ia|db|fd|ea)?|stm(ia|db|fd|ea)?|push|pop|ldrexh?|strexh?" \
    "|ldc2?l?|stc2?l?|vldr|vstr|vldm(ia|db)?|vstm(ia|db)?|vpush|vpop)" cond "$"
}
/^[0-9a-f]+ <[^>]+>:$/ { fn = $0; sub(/^[0-9a-f]+ </, "", fn); sub(/>:$/, "", fn); next }
/^ *[0-9a-f]+:\t/ {
  split($0, fld, "\t")
  m = fld[2]
  o = fld[3]
  c = fld[4]
  sub(/\.[nw]$/, "", m)
  sub(/\.(32|64|f32|f64)$/, "", m)
  if (m !~ class) next
  total++
  if (m ~ /^v?(push|pop)/ || (m ~ /^v?(ldm|stm)/ && o ~ /^sp!?,/)) { onsp++; next }
  if (match(o, /\[sp(, #-?(0x)?[0-9a-f]+)?\]/)) {
    off = substr(o, RSTART, RLENGTH)
    sub(/^\[sp(, #-?)?/, "", off)
    sub(/\]$/, "", off)
    v = (off ~ /^0x/) ? hexval(substr(off, 3)) : off + 0
    if (v >= 0 && v % 4 == 0) { onsp++; next }
  }
  if (o ~ /\[pc, #-?[0-9]+\]/ && match(c, /^@ \(?[0-9a-f]+ /)) {
    a = substr(c, 3, RLENGTH - 3)
    sub(/^\(/, "", a)
    a = hexval(a)
    if (a >= 0 && a % 4 == 0) { literal++; next }
  }
  other++
  print "access-check: " fn ": " $0 > "/dev/stderr"
}
END {
  printf "%d instructions that require a word-aligned address: %d based on sp, %d on aligned" \
    " literals, %d other\n", total, onsp, literal, other
  if (other > 0) {
    print "access-check: the instructions above may access an unaligned address" > "/dev/stderr"
    exit 1
  }
}
' "$1"
