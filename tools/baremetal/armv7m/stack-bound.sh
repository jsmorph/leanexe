#!/usr/bin/env bash
# A static bound on the stack of the functions in CompCert's Thumb-2 assembly for ARMv7-M and of
# the run-time functions that they reach (docs/native-bare-metal.md, the section on the stack).
# A function of the assembly is a label that a ".type NAME, %function" names.  Its frame is the
# sum of its ".cfi_adjust_cfa_offset" directives, which arm/Asmexpand.ml emits for the whole
# allocation of a frame and for the registers that a variadic function pushes (lines 581 to
# 600), and its callees are the targets of its "bl" and "b" instructions that name functions.
# DISASM is the output of objdump -d for the linked image.  A function that the assembly calls
# but does not define, such as CompCert's run-time function __compcert_i64_udiv, is taken from
# DISASM, where it begins at its symbol.  Its frame is the sum of the bytes that its push, stmdb
# sp!, vpush, vstmdb sp!, sub sp, and stores with a negative pre-indexed offset from sp allocate,
# a bound that ignores the instructions that free stack, and its callees are the targets of its
# "bl" and of its branches to other functions.  The script fails when such a function changes sp in
# another way, branches into the middle of another function, calls through a register, or
# writes pc other than by "bx lr" or a pop.  The bound excludes the frame that the processor
# pushes on an exception, since the startup code enables no interrupt and a fault ends the
# program.  DEPTHS lists the functions that take the call depth, one per line: each traps when
# the depth reaches 1,000 (depthLimit of Verified/Compile.lean), after its prologue, and passes
# the depth plus one to the functions of the list that it calls, so at most 1,001 of their frames
# nest.  A function outside the list calls one in it with depth 0, so a new chain of 1,001
# starts there.  The bound of a function is the deepest chain of frames from it under these
# rules, with the depth 0 for a function of the list.  The script fails when a function on a
# cycle of the call graph is not in the list, when a function calls one that neither the files
# nor DISASM define or calls through a register, or when the bound of ROOT exceeds LIMIT bytes.
# It prints the bound of ROOT, or of every function of the files and of DISASM that they reach,
# one per line, followed by the name.
# Usage: tools/baremetal/armv7m/stack-bound.sh [-r ROOT] [-l LIMIT] [-d DISASM] DEPTHS FILE.s...
set -euo pipefail
usage() {
  echo "usage: tools/baremetal/armv7m/stack-bound.sh [-r ROOT] [-l LIMIT] [-d DISASM] DEPTHS" \
    "FILE.s..." >&2
  exit 2
}
root=""
limit=""
disasm=/dev/null
while getopts "r:l:d:" opt; do
  case "$opt" in
    r) root=$OPTARG ;;
    l) limit=$OPTARG ;;
    d) disasm=$OPTARG ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ "$#" -ge 2 ] || usage
depths=$1
shift
awk -v depths="$depths" -v disasm="$disasm" -v root="$root" -v limit="$limit" -v maxdepth=1000 '
function fail(msg) { print "stack-bound: " msg > "/dev/stderr"; failed = 1 }

# The bound of a function outside the list.
function plain(f,   i, g, best, v) {
  if (f in pmemo) return pmemo[f]
  best = 0
  for (i = 1; i <= ncalls[f]; i++) {
    g = callee[f, i]
    v = (g in deep) ? chain(g, maxdepth) : plain(g)
    if (v > best) best = v
  }
  pmemo[f] = frame[f] + best
  return pmemo[f]
}

# The bound of a function of the list called with k increments of the depth left.
function chain(f, k,   i, g, best, v, key) {
  key = f SUBSEP k
  if (key in cmemo) return cmemo[key]
  best = 0
  if (k > 0)
    for (i = 1; i <= ncalls[f]; i++) {
      g = callee[f, i]
      v = (g in deep) ? chain(g, k - 1) : plain(g)
      if (v > best) best = v
    }
  cmemo[key] = frame[f] + best
  return cmemo[key]
}

function bound(f) { return (f in deep) ? chain(f, maxdepth) : plain(f) }

function addcall(f, g) {
  if (!((f, g) in called)) {
    called[f, g] = 1
    ncalls[f]++
    callee[f, ncalls[f]] = g
  }
}

# The number of registers in the list {...} of s, counting a range such as d8-d15.
function nregs(s,   l, parts, i, n, a, b) {
  l = s
  sub(/^[^{]*\{/, "", l)
  sub(/\}.*$/, "", l)
  n = 0
  for (i = split(l, parts, /, */); i > 0; i--) {
    if (parts[i] ~ /^[a-z]+[0-9]+-[a-z]+[0-9]+$/) {
      a = parts[i]; sub(/-.*$/, "", a); gsub(/[a-z]/, "", a)
      b = parts[i]; sub(/^.*-/, "", b); gsub(/[a-z]/, "", b)
      n += b - a + 1
    } else n++
  }
  return n
}

# The value of a decimal or hexadecimal immediate such as "#16" or "#0x10".
function imm(s,   v, i, c) {
  sub(/^#/, "", s)
  if (s !~ /^0x/) return s + 0
  v = 0
  for (i = 3; i <= length(s); i++) {
    c = index("0123456789abcdef", tolower(substr(s, i, 1)))
    if (c == 0) return -1
    v = v * 16 + c - 1
  }
  return v
}

# The bytes that an instruction of DISASM with mnemonic m and operands o allocates on the stack,
# 0 for one that frees stack or leaves sp alone, and -1 for one that changes sp in another way.
function alloc(m, o,   n) {
  if (m == "push" || (m ~ /^stm(db|fd)$/ && o ~ /^sp!, \{/)) return 4 * nregs(o)
  if (m == "vpush" || (m == "vstmdb" && o ~ /^sp!, \{/))
    return (o ~ /\{d/ ? 8 : 4) * nregs(o)
  if (m ~ /^str/ && match(o, /\[sp, #-[0-9]+\]!$/)) return substr(o, RSTART + 7, RLENGTH - 9) + 0
  if (m ~ /^subw?s?$/ && o ~ /^sp, (sp, )?#(0x)?[0-9a-f]+$/) {
    n = o; sub(/^.*#/, "#", n)
    return imm(n)
  }
  if (m == "pop" || m == "vpop" || (m ~ /^v?ldm(ia|fd)?$/ && o ~ /^sp!, \{/)) return 0
  if (m ~ /^addw?s?$/ && o ~ /^sp, (sp, )?#(0x)?[0-9a-f]+$/) return 0
  if (m ~ /^ldr/ && o ~ /\[sp\], #[0-9]+$/) return 0
  if (o ~ /\[sp[^]]*\]!|\[sp\], |sp!/) return -1
  if (o ~ /^sp(,|$)/ && m !~ /^(str|vstr|cmp|cmn|tst|teq)/) return -1
  return 0
}

BEGIN {
  while ((getline line < depths) > 0) if (line != "") deep[line] = 1
  close(depths)
  cond = "(eq|ne|cs|hs|cc|lo|mi|pl|vs|vc|hi|ls|ge|lt|gt|le|al)?"
  dcur = ""
  while ((getline line < disasm) > 0) {
    if (line ~ /^[0-9a-f]+ <[^>]+>:$/) {
      dcur = line
      sub(/^[0-9a-f]+ </, "", dcur)
      sub(/>:$/, "", dcur)
      if (dcur in dfun) ddup[dcur] = 1
      dfun[dcur] = 1
      dframe[dcur] = 0
      continue
    }
    if (dcur == "" || line !~ /^ *[0-9a-f]+:\t/) continue
    n = split(line, fld, "\t")
    m = fld[2]
    o = (n >= 3) ? fld[3] : ""
    if (m == ".word" || m == ".short" || m == ".byte") continue
    sub(/\.[nw]$/, "", m)
    a = alloc(m, o)
    if (a < 0) { dbad[dcur] = dbad[dcur] "; changes sp in \"" m " " o "\""; continue }
    dframe[dcur] += a
    if (m == "bl" || m ~ ("^b" cond "$") || m ~ /^cbn?z$/) {
      t = o
      sub(/^.*</, "", t)
      sub(/>.*$/, "", t)
      base = t
      sub(/\+0x[0-9a-f]+$/, "", base)
      if (base == dcur && m != "bl") continue
      if (t != base) { dbad[dcur] = dbad[dcur] "; branches into " t; continue }
      dncalls[dcur]++
      dcallee[dcur, dncalls[dcur]] = t
      continue
    }
    if (m ~ ("^bx" cond "$")) {
      if (o != "lr") dbad[dcur] = dbad[dcur] "; branches to " o
      continue
    }
    if (m ~ /^blx/) { dbad[dcur] = dbad[dcur] "; calls through " o; continue }
    if (o ~ /^pc,/ ||
        (o ~ /pc\}/ && m !~ ("^pop" cond "$") && !(m ~ /^ldm(ia|fd)?/ && o ~ /^sp!,/)))
      dbad[dcur] = dbad[dcur] "; writes pc in \"" m " " o "\""
  }
  close(disasm)
}
/^[A-Za-z_][A-Za-z0-9_]*:$/ {
  cur = substr($0, 1, length($0) - 1)
  if (cur in label) fail("two definitions of " cur)
  label[cur] = 1
  frame[cur] = 0
  ncalls[cur] = 0
  next
}
$1 == ".type" && $3 == "%function" { sub(/,$/, "", $2); isfun[$2] = 1; next }
$1 == ".cfi_adjust_cfa_offset" && cur != "" {
  if ($2 + 0 > 0) frame[cur] += $2
  next
}
$1 ~ ("^(bl|b" cond ")(\\.[nw])?$") && NF == 2 && $2 !~ /^\./ && cur != "" {
  addcall(cur, $2)
  next
}
$1 ~ /^blx/ && cur != "" { fail(cur " calls through a register"); next }
$1 ~ ("^bx" cond "$") && $2 != "lr" && cur != "" { fail(cur " branches to " $2); next }
END {
  for (f in isfun) if (!(f in label)) fail("no label for the function " f)
  n = 0
  for (f in isfun) for (i = 1; i <= ncalls[f]; i++) { n++; todo[n] = callee[f, i] }
  while (n > 0) {
    g = todo[n]
    n--
    if (g in isfun || g in external) continue
    if (!(g in dfun)) {
      fail("a function calls " g ", which neither the files nor the image define")
      continue
    }
    if (g in ddup) fail("the image defines " g " twice")
    if (g in dbad) fail(g substr(dbad[g], 2))
    external[g] = 1
    isfun[g] = 1
    frame[g] = dframe[g]
    ncalls[g] = 0
    for (i = 1; i <= dncalls[g]; i++) {
      addcall(g, dcallee[g, i])
      n++
      todo[n] = dcallee[g, i]
    }
  }
  for (f in isfun) {
    delete seen
    n = 0
    for (i = 1; i <= ncalls[f]; i++) { n++; todo[n] = callee[f, i] }
    cyclic = 0
    while (n > 0) {
      g = todo[n]
      n--
      if (g == f) { cyclic = 1; break }
      if (g in seen || !(g in isfun)) continue
      seen[g] = 1
      for (i = 1; i <= ncalls[g]; i++) { n++; todo[n] = callee[g, i] }
    }
    if (cyclic && !(f in deep)) fail(f " is on a cycle of calls but does not take the call depth")
  }
  if (failed) exit 1
  if (root != "") {
    if (!(root in isfun)) { fail("no function " root); exit 1 }
    b = bound(root)
    print b, root
    if (limit != "" && b > limit + 0) {
      fail("the bound " b " of " root " exceeds the stack of " limit " bytes")
      exit 1
    }
  } else {
    for (f in isfun) print bound(f), f
  }
}
' "$@"
