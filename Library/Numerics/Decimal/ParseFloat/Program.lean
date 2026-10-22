import Library.Numerics.Arithmetic.Uscale.Program
import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile
import LeanExe.Dialect.InsertErase
import LeanExe.Dialect.Float32

/-! Decimal and hexadecimal number strings to binary64 and binary32, rounded once to nearest with
ties to even, for strings of any length.  A string is an array of words, one byte per word.
`parse64 general s` and `parse32 general s` return `(true, w)` with the word `w` of the number
that `s` denotes in the grammar of `StrconvGrammar` (RFC 8259's number when `general` is false, the
general grammar otherwise), or `(false, 0)` when `s` is no number of the grammar.  The scanner
splits the string as `Library.Numerics.Decimal.Shared.StrconvDecode.decode` does.  Leading zeros of the significand are skipped,
the next 768 digits (113 for binary32) form the integer `D`, and a nonzero digit after them is
replaced by half a unit, which keeps the rounding (`StrconvTruncate`).  A decimal exponent beyond
the range of the format saturates.  A short decimal whose digits fit below `2 ^ 53` with a power of
ten from `10 ^ -22` to `10 ^ 22` takes Clinger's fast path, one binary64 multiplication or
division of exact values (W. D. Clinger, PLDI 1990).  Every other decimal is rounded exactly:
`Library.Numerics.Arithmetic.Uscale.scaledQuot` gives the quotient of the value in units of the least subnormal, scaled to
`p + 2` or `p + 3` bits, and whether the division leaves a remainder, which is Cox's unrounded form
(R. Cox, "Floating-Point Printing and Parsing Can Be Simple And Fast", 2026), and `roundUnits`
rounds it.  A hexadecimal significand keeps 15 significant hexadecimal digits and a sticky flag
and needs no division.  Signed exponents are carried with the bias `2 ^ 62`. -/

namespace Library.Numerics.Decimal.ParseFloat
open Library.Numerics.Arithmetic.Uscale

/-- Whether a word is an ASCII decimal digit. -/
def isDigitW (b : UInt64) : Bool := b - 0x30 < 10

/-- Whether a word is an ASCII hexadecimal digit. -/
def isHexW (b : UInt64) : Bool := b - 0x30 < 10 || (b ||| 0x20) - 0x61 < 6

/-- The value of a hexadecimal digit. -/
def hexValW (b : UInt64) : UInt64 := if b - 0x30 < 10 then b - 0x30 else (b ||| 0x20) - 0x57

/-- An ASCII letter in lower case; every other word unchanged. -/
def lowerW (b : UInt64) : UInt64 := if b - 0x41 < 26 then b + 0x20 else b

/-- The first position from `i` on whose byte is no digit of the class, or the end. -/
def span (s : Array UInt64) (hex : Bool) (i : UInt64) : UInt64 :=
  LeanExe.repeatWhile s.size.toUInt64 i
    (fun j => j < s.size.toUInt64 && (if hex then isHexW (limb s j) else isDigitW (limb s j)))
    (fun j => j + 1)

/-- Whether the bytes from `i` to the end, in lower case, are the `len ≤ 8` bytes of `w`, packed
least significant first. -/
def matchLower (s : Array UInt64) (i len w : UInt64) : Bool :=
  s.size.toUInt64 - i == len &&
    LeanExe.loop len true fun k ok => ok && lowerW (limb s (i + k)) == ((w >>> (8 * k)) &&& 0xFF)

/-- The value of an exponent's decimal digits from `j` to `k`, saturated at `10 ^ 11`. -/
def expDigits (s : Array UInt64) (j k : UInt64) : UInt64 :=
  LeanExe.loop (k - j) 0 fun t acc => min (10 * acc + (limb s (j + t) - 0x30)) 100000000000

/-- An exponent's optional sign and digits from `i` to the end: whether they are well formed,
whether the sign is negative, and the saturated value. -/
def expPart (s : Array UInt64) (i : UInt64) : Bool × Bool × UInt64 :=
  let c := limb s i
  let j := if c == 0x2D || c == 0x2B then i + 1 else i
  let k := span s false j
  (j < k && k == s.size.toUInt64, c == 0x2D, expDigits s j k)

/-- The position of digit `k` of a significand whose `ni` integer digits start at `i0`, past the
point after them. -/
def digitPos (i0 ni k : UInt64) : UInt64 := if k < ni then i0 + k else i0 + k + 1

/-- The number of leading zeros among the `total` digits. -/
def leadingZeros (s : Array UInt64) (i0 ni total : UInt64) : UInt64 :=
  LeanExe.repeatWhile total 0 (fun z => z < total && limb s (digitPos i0 ni z) == 0x30)
    (fun z => z + 1)

/-- Whether a digit from `a` to `b` is nonzero. -/
def anyNonzero (s : Array UInt64) (i0 ni a b : UInt64) : Bool :=
  LeanExe.loop (b - a) false fun t x => x || limb s (digitPos i0 ni (a + t)) != 0x30

/-- The value of the `len ≤ 9` decimal digits from digit `k`. -/
def chunkVal (s : Array UInt64) (i0 ni k len : UInt64) : UInt64 :=
  LeanExe.loop len 0 fun t acc => 10 * acc + (limb s (digitPos i0 ni (k + t)) - 0x30)

/-- The value of the `kept` decimal digits from digit `z`, as limbs, nine digits at a time. -/
def digitsVal (s : Array UInt64) (i0 ni z kept : UInt64) : Array UInt64 :=
  LeanExe.loop ((kept + 8) / 9) (LeanExe.build 0 fun _ => (0 : UInt64)) fun c acc =>
    mulSmall acc (pow10Word (min 9 (kept - 9 * c)))
      (chunkVal s i0 ni (z + 9 * c) (min 9 (kept - 9 * c)))

/-- The value of the `len ≤ 15` hexadecimal digits from digit `k`. -/
def hexVal (s : Array UInt64) (i0 ni k len : UInt64) : UInt64 :=
  LeanExe.loop len 0 fun t acc => 16 * acc + hexValW (limb s (digitPos i0 ni (k + t)))

/-- The encoding of `(u + φ) · 2 ^ (tb - 2 ^ 62)` units of the least subnormal, rounded to nearest
with ties to even in the format of precision `p` and infinity field `F`, where `φ` lies in `[0, 1)`
and is positive exactly when `sticky`; the encoding of infinity from the overflow threshold on. -/
def roundUnits (p F u : UInt64) (sticky : Bool) (tb : UInt64) : UInt64 :=
  if u == 0 then 0
  else
    let e := if wordBits u + tb ≤ p + 0x4000000000000000 then 1
      else wordBits u + tb - 0x4000000000000000 - p + 1
    if e ≥ F then F <<< (p - 1)
    else
      let q :=
        if tb ≤ e - 1 + 0x4000000000000000 then
          let r := e - 1 + 0x4000000000000000 - tb
          if r == 0 then u
          else if r ≥ 64 then 0
          else if ((1 : UInt64) <<< (r - 1)) < (u &&& (((1 : UInt64) <<< r) - 1)) ||
              ((u &&& (((1 : UInt64) <<< r) - 1)) == ((1 : UInt64) <<< (r - 1)) &&
                (sticky || (u >>> r) &&& 1 == 1)) then (u >>> r) + 1
          else u >>> r
        else u <<< (tb - 0x4000000000000000 - (e - 1))
      if (e - 1) * ((1 : UInt64) <<< (p - 1)) + q ≥ F <<< (p - 1) then F <<< (p - 1)
      else (e - 1) * ((1 : UInt64) <<< (p - 1)) + q

/-- The encoding of the positive decimal `(D + θ) · 10 ^ (qb - 2 ^ 62)`, where `D` has `kept`
digits, `θ` is 0 or lies strictly between 0 and 1 when `sticky`, in the format of precision `p`,
infinity field `F`, and least subnormal `2 ^ -nu`; the value is beyond the overflow threshold
from `10 ^ emax` on and below half the least subnormal from `10 ^ -emin` down. -/
def decRound (p F nu emax emin : UInt64) (D : Array UInt64) (kept qb : UInt64) (sticky : Bool) :
    UInt64 :=
  if kept == 0 then 0
  else if qb + kept ≥ 0x4000000000000001 + emax then F <<< (p - 1)
  else if qb + kept + emin ≤ 0x4000000000000000 then 0
  else
    let n := if qb ≥ 0x4000000000000000 then
        mulPow10 (if sticky then mulSmall D 2 1 else D) (qb - 0x4000000000000000)
      else if sticky then mulSmall D 2 1 else D
    let d := if qb ≥ 0x4000000000000000 then LeanExe.build 1 fun _ => if sticky then 2 else 1
      else mulPow10 (LeanExe.build 1 fun _ => if sticky then 2 else 1) (0x4000000000000000 - qb)
    let sn := if bitLen n ≤ bitLen d + p + 2 then bitLen d + p + 2 - bitLen n else 0
    let sd := if bitLen n ≤ bitLen d + p + 2 then 0 else bitLen n - bitLen d - p - 2
    let r := scaledQuot n d sn sd (p + 3)
    roundUnits p F r.1 r.2 (0x4000000000000000 + nu + sd - sn)

/-- The decimal significand and exponent from `i0`: whether they are well formed in the grammar,
the limbs of the first `K` significant digits, their count, the biased decimal exponent of the last
kept digit, and whether a dropped digit is nonzero. -/
def decParse (general : Bool) (K : UInt64) (s : Array UInt64) (i0 : UInt64) :
    Bool × Array UInt64 × UInt64 × UInt64 × Bool :=
  let i1 := span s false i0
  let pt := limb s i1 == 0x2E
  let i2 := if pt then span s false (i1 + 1) else i1
  let ni := i1 - i0
  let nf := if pt then i2 - i1 - 1 else 0
  let e := expPart s (i2 + 1)
  let z := leadingZeros s i0 ni (ni + nf)
  let kept := min (ni + nf - z) K
  ((if general then ni + nf != 0
      else (ni == 1 || (1 < ni && limb s i0 != 0x30)) && (!pt || nf != 0)) &&
    (i2 == s.size.toUInt64 || ((limb s i2 ||| 0x20) == 0x65 && e.1)),
   digitsVal s i0 ni z kept, kept,
   (if i2 != s.size.toUInt64 && e.2.1 then 0x4000000000000000 - e.2.2
    else if i2 == s.size.toUInt64 then 0x4000000000000000 else 0x4000000000000000 + e.2.2) -
     nf + (ni + nf - z - kept),
   anyNonzero s i0 ni (z + kept) (ni + nf))

/-- The hexadecimal significand and binary exponent from `i`: whether they are well formed, the
first 15 significant digits, whether a dropped digit is nonzero, and the biased binary exponent of
the last kept digit in units of `2 ^ -nu`. -/
def hexParse (nu : UInt64) (s : Array UInt64) (i : UInt64) : Bool × UInt64 × Bool × UInt64 :=
  let i1 := span s true i
  let pt := limb s i1 == 0x2E
  let i2 := if pt then span s true (i1 + 1) else i1
  let ni := i1 - i
  let nf := if pt then i2 - i1 - 1 else 0
  let e := expPart s (i2 + 1)
  let z := leadingZeros s i ni (ni + nf)
  let kept := min (ni + nf - z) 15
  (ni + nf != 0 && (limb s i2 ||| 0x20) == 0x70 && e.1,
   hexVal s i ni z kept,
   anyNonzero s i ni (z + kept) (ni + nf),
   (if e.2.1 then 0x4000000000000000 - e.2.2 else 0x4000000000000000 + e.2.2) - 4 * nf +
     4 * (ni + nf - z - kept) + nu)

/-- `10 ^ k` as a double, exact for `k ≤ 22`. -/
def pow10Float (k : UInt64) : Float := LeanExe.loop k 1.0 fun _ x => x * 10.0

/-- Clinger's fast path: `D · 10 ^ (qb - 2 ^ 62)` by one rounded operation, for `D < 2 ^ 53` and
an exponent from -22 to 22. -/
def fastPath (D : Array UInt64) (qb : UInt64) : UInt64 :=
  if qb ≥ 0x4000000000000000 then
    ((limb D 0 ||| (limb D 1 <<< 32)).toFloat * pow10Float (qb - 0x4000000000000000)).toBits
  else ((limb D 0 ||| (limb D 1 <<< 32)).toFloat / pow10Float (0x4000000000000000 - qb)).toBits

/-- The number `s` denotes as a binary64 word, or `(false, 0)`. -/
def parse64 (general : Bool) (s : Array UInt64) : Bool × UInt64 :=
  let neg := limb s 0 == 0x2D
  let i0 := if neg || (general && limb s 0 == 0x2B) then 1 else 0
  let sign := if neg then 0x8000000000000000 else 0
  if general && (matchLower s i0 3 0x666E69 || matchLower s i0 8 0x7974696E69666E69) then
    (true, sign ||| 0x7FF0000000000000)
  else if general && matchLower s i0 3 0x6E616E then (true, 0x7FF8000000000000)
  else if general && limb s i0 == 0x30 && (limb s (i0 + 1) ||| 0x20) == 0x78 then
    let h := hexParse 1074 s (i0 + 2)
    if h.1 then (true, sign ||| roundUnits 53 2047 h.2.1 h.2.2.1 h.2.2.2) else (false, 0)
  else
    let d := decParse general 768 s i0
    if !d.1 then (false, 0)
    else if !d.2.2.2.2 && bitLen d.2.1 ≤ 53 && 0x3FFFFFFFFFFFFFEA ≤ d.2.2.2.1 &&
        d.2.2.2.1 ≤ 0x4000000000000016 then (true, sign ||| fastPath d.2.1 d.2.2.2.1)
    else (true, sign ||| decRound 53 2047 1074 309 325 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2)

/-- The number `s` denotes as a binary32 word in the low 32 bits of the result, or `(false, 0)`. -/
def parse32 (general : Bool) (s : Array UInt64) : Bool × UInt64 :=
  let neg := limb s 0 == 0x2D
  let i0 := if neg || (general && limb s 0 == 0x2B) then 1 else 0
  let sign := if neg then 0x80000000 else 0
  if general && (matchLower s i0 3 0x666E69 || matchLower s i0 8 0x7974696E69666E69) then
    (true, sign ||| 0x7F800000)
  else if general && matchLower s i0 3 0x6E616E then (true, 0x7FC00000)
  else if general && limb s i0 == 0x30 && (limb s (i0 + 1) ||| 0x20) == 0x78 then
    let h := hexParse 149 s (i0 + 2)
    if h.1 then (true, sign ||| roundUnits 24 255 h.2.1 h.2.2.1 h.2.2.2) else (false, 0)
  else
    let d := decParse general 113 s i0
    if !d.1 then (false, 0)
    else (true, sign ||| decRound 24 255 149 39 46 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2)

end Library.Numerics.Decimal.ParseFloat
