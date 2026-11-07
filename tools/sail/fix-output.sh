#!/bin/sh
# Usage: fix-output.sh DIR LIB
# Edits the Lean output of Sail 0.20.3 (root module DIR/LIB.lean, modules in DIR/LIB) so that it
# elaborates, and prints the number of rewrites of each edit.  Each edit keeps the meaning of the
# definitions:
#  - Real.lean, written by --lean-real-numbers, opens a namespace Defs that no output declares,
#    and Lean rejects the open.  The script deletes the line.
#  - Lean v4.34 parses `assert` at the start of a do element as its own assert element, so a call
#    of the model's assert there fails; the script qualifies every call as LIB.assert.
#  - The back end prints a real literal with Zarith's Q.to_string, as -?N or -?N/D without
#    parentheses (pretty_print_lean.ml, doc_lit), so `gt_real e 1/2` parses as an application
#    divided by 2.  Outside strings and comments, the script parenthesizes every N/D and -N/D
#    and every -N that no parenthesis precedes, the only other forms that Q.to_string prints
#    being N, which needs no parentheses.  A negative integer literal prints as (-N)
#    (doc_big_int).  The script fails if a decimal or exponent literal appears, a form that it
#    does not handle.
set -eu
dir=$1
lib=$2
opens=0
if [ -f "$dir/$lib/Real.lean" ]; then
  opens=$(grep -c '^open Defs$' "$dir/$lib/Real.lean" || true)
  sed -i '/^open Defs$/d' "$dir/$lib/Real.lean"
fi
asserts=$(grep -o '\bassert ' "$dir/$lib.lean" | wc -l)
sed -i "s/\\bassert /$lib.assert /g" "$dir/$lib.lean"
echo "fix-output.sh: open Defs deleted: $opens"
echo "fix-output.sh: assert calls qualified: $asserts"
for f in "$dir/$lib.lean" "$dir/$lib/Defs.lean" "$dir/$lib/SpecializationV1.lean"; do
  [ -f "$f" ] || continue
  perl -e '
    my $src = do { local $/; <> };
    my ($out, $frac, $neg, $bad) = ("", 0, 0, 0);
    # Code, strings, line comments, and block comments, in order.
    while ($src =~ /\G((?:[^"\/-]|\/(?!-)|-(?![-\/]))+|"(?:[^"\\]|\\.)*"|--[^\n]*|\/-.*?-\/|.)/gs) {
      my $seg = $1;
      if ($seg =~ /^(?:"|--|\/-)/) { $out .= $seg; next; }
      $bad += () = $seg =~ /(?<![\w.\x27])\d+(?:\.\d+[eE]?|[eE][-+]?\d)/g;
      $frac += $seg =~ s/(?<![\w.\x27\/])(-?\d+\/\d+)(?![\w.\x27\/])/($1)/g;
      $neg += $seg =~ s/(?<![\w.\x27)\](\/])(-\d+)(?![\w.\x27\/])/($1)/g;
      $out .= $seg;
    }
    if ($bad) { print STDERR "fix-output.sh: $bad literals of an unhandled form\n"; exit 1; }
    print $out;
    print STDERR "fix-output.sh: real literals parenthesized: $frac fractions, $neg negative\n";
  ' "$f" >"$f.fixed" || { rm -f "$f.fixed"; echo "fix-output.sh: $f" >&2; exit 1; }
  mv "$f.fixed" "$f"
done
