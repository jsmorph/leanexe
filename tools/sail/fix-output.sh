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
#  - The back end writes an integer of the model where Lean expects a natural number, as a width,
#    an index, a shift, or a fuel, and lean-sail v6 converts it with its coercion
#    `CoeT Int x Nat` (`x.toNat`), which maps a negative integer to 0; asl_Int's `result` even
#    takes the type Nat from its first branch, so that SInt of a negative vector became 0.
#    lean-sail-v6.diff deletes the coercion, and the script writes each conversion out: the type
#    Int where the model's value is an integer, and `.toNat` where the model guarantees a
#    nonnegative value, each with the guarantee in a comment below.  `.toNat` elaborates to the
#    term that the coercion gave, so only asl_Int changes meaning.
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

# conv OLD NEW COUNT: replaces the text OLD, which must occur COUNT times in $dir/$lib.lean, with
# NEW.
convs=0
conv() {
  n=$(OLD=$1 perl -0777 -ne '$c = () = /\Q$ENV{OLD}\E/g; print $c' "$dir/$lib.lean")
  if [ "$n" != "$3" ]; then
    echo "fix-output.sh: $n occurrences of '$1', expected $3" >&2
    exit 1
  fi
  OLD=$1 NEW=$2 perl -0777 -pi -e 's/\Q$ENV{OLD}\E/$ENV{NEW}/g' "$dir/$lib.lean"
  convs=$((convs + n))
}
# asl_Int (sail-arm prelude.sail, `Int`): `result` is an integer.
conv '  let result ← do
    if (is_unsigned : Bool)' '  let result : Int ← do
    if (is_unsigned : Bool)' 1
# integer_subrange (prelude.sail): its type requires 'lo <= 'hi; every call in the slice passes
# lo = 0, and integer_access passes its index as lo, which every call gives as 0.  The width
# converts hi and lo, as the coercion converted the operands of a type's arithmetic.
conv ': (BitVec (hi - lo + 1)) :=
  (get_slice_int ((hi -i lo) +i 1) i lo)' ': (BitVec (hi.toNat - lo.toNat + 1)) :=
  (get_slice_int ((hi -i lo) +i 1).toNat i lo.toNat)' 1
# integer_update_subrange (prelude.sail): its type requires 0 <= 'o <= 'm.
conv '(set_slice_int ((hi -i lo) +i 1) i lo x)' '(set_slice_int ((hi -i lo) +i 1).toNat i lo x)' 1
# to_bytes_le and from_bytes_le (Sail's vector.sail): the loop index runs from 0, and 'n > 0.  No
# function of F7 reaches either.
conv '(vectorUpdate res i (Sail.BitVec.extractLsb b ((8 *i i) +i 7) (8 *i i)))' \
  '(vectorUpdate res i.toNat (Sail.BitVec.extractLsb b ((8 *i i) +i 7).toNat (8 *i i).toNat))' 1
conv '(BitVec.zero (8 *i n))' '(BitVec.zero (8 *i n).toNat)' 1
conv '(Sail.BitVec.updateSubrange res ((8 *i i) +i 7) (8 *i i) (GetElem?.getElem! v i))' \
  '(Sail.BitVec.updateSubrange res ((8 *i i) +i 7).toNat (8 *i i).toNat (GetElem?.getElem! v i))' 1
# slice_zeros_concat and subrange_zeros_concat (mono_rewrites.sail): their types require
# 'p + 'q >= 0 and 'hi - 'lo + 1 + 'q >= 0, which do not bound each operand, and the widths
# convert each operand, as the coercion did.  No function of F7 reaches either.
conv ": (BitVec (l + l')) :=" ": (BitVec (l.toNat + l'.toNat)) :=" 1
conv "(extzv (m := (l +i l')) xs)" "(extzv (m := (l +i l').toNat) xs)" 1
conv ": (BitVec (hi - lo + 1 + l')) :=" ": (BitVec (hi.toNat - lo.toNat + 1 + l'.toNat)) :=" 1
# sext_slice (mono_rewrites.sail): no type constraint bounds l by the width, and the conversion
# maps a negative shift to 0.  No function of F7 reaches sext_slice.
conv '((Sail.BitVec.length xs) -i l))
  (extsv (m := m) xs)' '((Sail.BitVec.length xs) -i l).toNat)
  (extsv (m := m) xs)' 1
# unsigned_subrange (mono_rewrites.sail): its type requires ('i - 'j) >= 0.
conv '(pow2 ((i -i j) +i 1))' '(pow2 ((i -i j) +i 1).toNat)' 1
# vector_update_subrange_from_integer_subrange (mono_rewrites.sail): its type requires
# 0 <= 'e2 <= 's2.
conv 'v1 s1 e1 v2 (s2 -i e2) 0)' 'v1 s1 e1 v2 (s2 -i e2).toNat 0)' 1
# FPInfinity, FPMaxNormal, FPZero, and FPDefaultNaN__1 (v8_base.sail): each asserts
# N in {16, 32, 64} and sets E to 5, 8, or 11, so E - 1 >= 4 and F = N - (E + 1) is 10, 23, or 52.
conv '  let exp : (BitVec E) := (Ones (n := E))' \
  '  let exp : (BitVec E.toNat) := (Ones (n := E.toNat))' 2
conv '  let frac : (BitVec F) := (Zeros (n := F))' \
  '  let frac : (BitVec F.toNat) := (Zeros (n := F.toNat))' 2
conv '  let exp : (BitVec E) := ((Ones (n := (E -i 1))) +++ 0#1)' \
  '  let exp : (BitVec E.toNat) := ((Ones (n := (E -i 1).toNat)) +++ 0#1)' 1
conv '  let frac : (BitVec F) := (Ones (n := F))' \
  '  let frac : (BitVec F.toNat) := (Ones (n := F.toNat))' 1
conv '  let exp : (BitVec E) := (Zeros (n := E))' \
  '  let exp : (BitVec E.toNat) := (Zeros (n := E.toNat))' 1
conv '  let frac : (BitVec F) := (1#1 +++ (Zeros (n := (F -i 1))))' \
  '  let frac : (BitVec F.toNat) := (1#1 +++ (Zeros (n := (F -i 1).toNat)))' 1
# FPProcessException (v8_base.sail): the case statement sets cumul to 0, 1, 2, 3, 4, or 7, and
# enable is cumul + 8.
conv '(BitVec.access fpcr enable)' '(BitVec.access fpcr enable.toNat)' 1
conv '(BitVec.update accumulated_exceptions cumul (Bit 1#1))' \
  '(BitVec.update accumulated_exceptions cumul.toNat (Bit 1#1))' 1
conv '(FPSCR_read__1 ())) cumul cumul 1#1)' '(FPSCR_read__1 ())) cumul.toNat cumul.toNat 1#1)' 1
conv '(BitVec.update (← readReg FPSR) cumul (Bit 1#1))' \
  '(BitVec.update (← readReg FPSR) cumul.toNat (Bit 1#1))' 1
# FPRoundBase__1 (v8_base.sail): it asserts op != 0 and sets mantissa to the absolute value of op,
# so the measures of fp-measures.sail, ceil(1 / mantissa) and ceil(mantissa), are positive.
conv '(fuel :=(round_up (div_real (to_real 1) mantissa)))' \
  '(fuel :=(round_up (div_real (to_real 1) mantissa)).toNat)' 1
conv '(fuel :=(round_up mantissa))' '(fuel :=(round_up mantissa).toNat)' 1
# FPRoundBase__1: an assertion N - (E + F + 1) >= 0 precedes each concatenation of the result, and
# N >= 16.
conv '(Zeros (n := (N -i ((E +i F) +i 1))))' '(Zeros (n := (N -i ((E +i F) +i 1)).toNat))' 2
conv '(sign +++ (Ones (n := (N -i 1))))' '(sign +++ (Ones (n := (N -i 1).toNat)))' 1
# FPProcessNaN__1 (v8_base.sail): it asserts 0 <= topfrac < the width of result.
conv '(BitVec.update result topfrac (Bit 1#1))' '(BitVec.update result topfrac.toNat (Bit 1#1))' 1
echo "fix-output.sh: integers converted explicitly: $convs"
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
