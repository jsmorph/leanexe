#!/bin/sh
# Usage: check.sh FPEMU VECTORS OUT
# Runs the emulator FPEMU (build.sh) on the vector file VECTORS, writing its lines to OUT, and
# compares each result with the line's Talos result and, where the line has one, with the
# rational Lean evaluation's result.  For each form and class, the script prints the number of
# vectors, the number whose result equals TALOS, and the number whose result equals MODEL (or
# "-" when the class has no MODEL results).  For FPSqrt it adds the vectors that reach sqrt_real,
# the unresolved ones (fpemu.c), the vectors that equal TALOS and are not unresolved, and the
# smallest lower bounds of the margin as a multiple of sqrt_real's tolerance and of half an ulp.
# It lists up to 20 disagreements and every unresolved vector, and exits with status 1 if any
# result disagrees, any vector is unresolved, or OUT and VECTORS differ in their numbers of lines.
set -eu
emu=$1
vectors=$2
out=$3
"$emu" "$vectors" >"$out"
want=$(wc -l <"$vectors")
got=$(wc -l <"$out")
if [ "$want" -ne "$got" ]; then
  echo "check.sh: $vectors has $want lines, $out $got" >&2
  exit 1
fi
awk '
  {
    key = $1 " " $2
    if (!(key in n)) order[++keys] = key
    n[key]++
    if ($7 == $5) talos[key]++
    if ($6 != "-") { hasmodel[key] = 1; if ($7 == $6) model[key]++ }
    bad = $7 != $5 || ($6 != "-" && $7 != $6)
    if ($1 == "fsqrt" && $8 != "none") {
      sq[key]++
      if ($8 == "unresolved") {
        unres[key]++
        unresolved++
        print "unresolved: " $0
      }
      if (!(key in minr) || $9 + 0 < minr[key] + 0) { minr[key] = $9; minrv[key] = $3 }
      if (!(key in minh) || $10 + 0 < minh[key] + 0) { minh[key] = $10; minhv[key] = $3 }
    }
    if ($1 == "fsqrt" && $7 == $5 && $8 != "unresolved") agree[key]++
    if (bad) {
      disagreements++
      if (disagreements <= 20) print "disagreement: " $0
    }
  }
  END {
    printf "%-6s %-10s %8s %8s %8s\n", "form", "class", "vectors", "=talos", "=model"
    for (i = 1; i <= keys; i++) {
      k = order[i]
      split(k, f, " ")
      printf "%-6s %-10s %8d %8d %8s\n", f[1], f[2], n[k], talos[k] + 0, \
        (k in hasmodel) ? model[k] + 0 : "-"
    }
    printf "\n%-6s %-10s %8s %8s %10s %8s %12s %16s %12s %16s\n", "form", "class", "vectors", \
      "sqrt", "unresolved", "agree", "min ratio", "at", "min halfulp", "at"
    for (i = 1; i <= keys; i++) {
      k = order[i]
      split(k, f, " ")
      if (f[1] != "fsqrt") continue
      if (k in sq)
        printf "%-6s %-10s %8d %8d %10d %8d %12s %16s %12s %16s\n", f[1], f[2], n[k], sq[k], \
          unres[k] + 0, agree[k] + 0, minr[k], minrv[k], minh[k], minhv[k]
      else
        printf "%-6s %-10s %8d %8d %10d %8d %12s %16s %12s %16s\n", f[1], f[2], n[k], 0, 0, \
          agree[k] + 0, "-", "-", "-", "-"
    }
    printf "\n%d vectors, %d disagreements, %d unresolved\n", NR, disagreements, unresolved
    exit (disagreements > 0 || unresolved > 0)
  }
' "$out"
