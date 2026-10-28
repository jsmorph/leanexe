#!/usr/bin/env bash
# A static bound on the stack of the functions in CompCert's assembly for AArch64
# (docs/native-bare-metal.md, the section on the stack).  A function is a label that a
# ".type NAME, @function" names.  Its frame is the sum of its ".cfi_adjust_cfa_offset"
# directives, which aarch64/Asmexpand.ml emits for each part of a frame's allocation (lines 491 to
# 516), and its callees are the targets of its "bl" and "b" instructions that name functions.
# DEPTHS lists the functions that take the call depth, one per line, as native-verified and
# native-bare write them: each traps when the depth reaches 1,000 (depthLimit of
# Verified/Compile.lean), after its prologue, and passes the depth plus one to the functions of
# the list that it calls, so at most 1,001 of their frames nest.  A function outside the list
# calls one in it with depth 0, so a new chain of 1,001 starts there.  The bound of a function is
# the deepest chain of frames from it under these rules, with the depth 0 for a function of the
# list.  The script fails when a function on a cycle of the call graph is not in the list, since
# its recursion would have no bound, when a function calls one that the files do not define or
# calls through a register, or when the bound of ROOT exceeds LIMIT bytes.  It prints the bound
# of ROOT, or of every function, one per line, followed by the name.
# Usage: tools/baremetal/stack-bound.sh [-r ROOT] [-l LIMIT] DEPTHS FILE.s...
set -euo pipefail
usage() {
  echo "usage: tools/baremetal/stack-bound.sh [-r ROOT] [-l LIMIT] DEPTHS FILE.s..." >&2
  exit 2
}
root=""
limit=""
while getopts "r:l:" opt; do
  case "$opt" in
    r) root=$OPTARG ;;
    l) limit=$OPTARG ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ "$#" -ge 2 ] || usage
depths=$1
shift
awk -v depths="$depths" -v root="$root" -v limit="$limit" -v maxdepth=1000 '
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

BEGIN {
  while ((getline line < depths) > 0) if (line != "") deep[line] = 1
  close(depths)
}
/^[A-Za-z_][A-Za-z0-9_]*:$/ {
  cur = substr($0, 1, length($0) - 1)
  if (cur in label) fail("two definitions of " cur)
  label[cur] = 1
  frame[cur] = 0
  ncalls[cur] = 0
  next
}
$1 == ".type" && $3 == "@function" { sub(/,$/, "", $2); isfun[$2] = 1; next }
$1 == ".cfi_adjust_cfa_offset" && cur != "" {
  if ($2 + 0 > 0) frame[cur] += $2
  next
}
($1 == "bl" || $1 == "b") && NF == 2 && $2 !~ /^\./ && cur != "" {
  if (!((cur, $2) in called)) {
    called[cur, $2] = 1
    ncalls[cur]++
    callee[cur, ncalls[cur]] = $2
  }
  next
}
($1 == "blr" || $1 == "br") && cur != "" { fail(cur " calls through a register"); next }
END {
  for (f in isfun) if (!(f in label)) fail("no label for the function " f)
  for (f in isfun)
    for (i = 1; i <= ncalls[f]; i++)
      if (!(callee[f, i] in isfun)) fail(f " calls " callee[f, i] ", which the files do not define")
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
