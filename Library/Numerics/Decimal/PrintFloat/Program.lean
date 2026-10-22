import Library.Numerics.Arithmetic.Uscale.Program
import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile
import LeanExe.Dialect.InsertErase
import LeanExe.Dialect.Float32

/-! Binary64 and binary32 words to decimal strings: the shortest decimal that rounds to the word,
the nearest to the word's value among the shortest, with an even last digit at a tie, written in
a scientific layout (`print64`, `print32`) or in the layout of ECMA-262's Number::toString
(`print64Ecma`, `print32Ecma`).  A string is an array of words, one byte per word.  A finite
nonzero word of significand `Q` in binade `E` has a rounding interval whose ends, in quarter
units of the least subnormal, are `4 Q - 2` (or `4 Q - 1` at the start of a normal binade) and
`4 Q + 2` times `2 ^ (E - 1)`, with the ends included when `Q` is even.  `shortest` finds the
largest exponent `J` for which a multiple of `10 ^ J` lies in the interval, searching down from an
exponent above the interval's upper end, and takes the multiple nearest to the value; when that
multiple has one digit, a one-digit multiple of `10 ^ (J - 1)` can also lie in the interval, and
the nearer of the two is taken.  Every comparison is an exact quotient with its remainder flag from
`Library.Numerics.Arithmetic.Uscale.Uscale.scaledQuot`.  The non-finite words print as `NaN`, `Infinity`, and `-Infinity`, and the
zeros as `0e0` and `-0e0` (scientific) or `0` and `-0` (ECMAScript). -/

namespace Library.Numerics.Decimal.PrintFloat.PrintFloat
open Library.Numerics.Arithmetic.Uscale.Uscale

/-- The limbs of a word below `2 ^ 64`. -/
def limbsOf (x : UInt64) : Array UInt64 :=
  LeanExe.build 2 fun i => if i == 0 then x &&& 0xFFFFFFFF else x >>> 32

/-- `⌊N · 2 ^ sn / (2 ^ sd · 10 ^ (jb - 2 ^ 62))⌋` and whether a remainder is left, for the
biased decimal exponent `jb`. -/
def quotAt (N sn sd jb : UInt64) : UInt64 × Bool :=
  if jb ≥ 0x4000000000000000 then
    scaledQuot (limbsOf N) (mulPow10 (LeanExe.build 1 fun _ => (1 : UInt64)) (jb - 0x4000000000000000))
      sn sd 63
  else scaledQuot (mulPow10 (limbsOf N) (0x4000000000000000 - jb))
      (LeanExe.build 1 fun _ => (1 : UInt64)) sn sd 63

/-- The least multiplier `m` of `10 ^ (jb - 2 ^ 62)` with `m · 10 ^ j` in the interval, and the
greatest one plus one, for the interval of quarter-unit ends `Nl` and `Nh` scaled by `2 ^ sn` and
`2 ^ -sd`, ends included when `closed`. -/
def range (Nl Nh sn sd jb : UInt64) (closed : Bool) : UInt64 × UInt64 :=
  let l := quotAt Nl sn sd jb
  let h := quotAt Nh sn sd jb
  (if closed && !l.2 then l.1 else l.1 + 1, if !closed && !h.2 then h.1 else h.1 + 1)

/-- Whether a multiple of `10 ^ (jb - 2 ^ 62)` lies in the interval. -/
def found (Nl Nh sn sd jb : UInt64) (closed : Bool) : Bool :=
  let r := range Nl Nh sn sd jb closed
  r.1 < r.2

/-- The integer nearest to `v`, the even one at a tie, from `⌊2 v⌋` and whether `2 v` is not an
integer. -/
def nearest (f2 : UInt64) (r2 : Bool) : UInt64 :=
  if f2 &&& 1 == 0 then f2 >>> 1
  else if r2 then (f2 >>> 1) + 1
  else if (f2 >>> 1) &&& 1 == 0 then f2 >>> 1 else (f2 >>> 1) + 1

/-- `m` clamped into `[lo, hi - 1]`. -/
def clamp (m lo hi1 : UInt64) : UInt64 := if m < lo then lo else if m + 1 > hi1 then hi1 - 1 else m

/-- A biased decimal exponent `j` with `10 ^ (j - 1)` above the interval's upper end
`Nh · 2 ^ (sn - sd)`, which lies below `2 ^ B` for `B = bits(Nh) + sn - sd`: `j = ⌈31 B / 100⌉`
for `B ≥ 0` and `j = -⌊3 |B| / 10⌋` otherwise, since `2 ^ 100 < 10 ^ 31` and `10 ^ 3 < 2 ^ 10`. -/
def startExp (Nh sn sd : UInt64) : UInt64 :=
  let b := wordBits Nh + sn
  if b ≥ sd then 0x4000000000000000 + ((b - sd) * 31 + 99) / 100
  else 0x4000000000000000 - ((sd - b) * 3) / 10

/-- The shortest decimal of the word of significand `Q` in binade `E` of a format whose least
subnormal is `2 ^ -nu`, nearest to the value at a tie of length, as `(t, kb)` with the value
`t · 10 ^ (kb - 2 ^ 62)`; `low` marks the start of a normal binade. -/
def shortest (Q E nu : UInt64) (low : Bool) : UInt64 × UInt64 :=
  let Nv := 4 * Q
  let Nh := 4 * Q + 2
  let Nl := if low then 4 * Q - 1 else 4 * Q - 2
  let sn := E - 1
  let sd := nu + 2
  let closed := Q &&& 1 == 0
  let j0 := startExp Nh sn sd
  let i := LeanExe.repeatWhile 2000 0 (fun i => i < 2000 && !found Nl Nh sn sd (j0 - i) closed)
    (fun i => i + 1)
  let J := j0 - i
  let r := range Nl Nh sn sd J closed
  let v := quotAt Nv (sn + 1) sd J
  let m := clamp (nearest v.1 v.2) r.1 r.2
  if m < 10 then
    let r' := range Nl Nh sn sd (J - 1) closed
    let hi' := min r'.2 10
    if r'.1 < hi' then
      let v' := quotAt Nv (sn + 1) sd (J - 1)
      let m' := clamp (nearest v'.1 v'.2) r'.1 hi'
      if v'.1 < m' + 10 * m then (m', J - 1) else (m, J)
    else (m, J)
  else (m, J)

/-- The number of decimal digits of `t ≥ 1`, for `t < 10 ^ 19`. -/
def numDigits (t : UInt64) : UInt64 :=
  LeanExe.repeatWhile 19 1 (fun k => k < 19 && pow10Word k ≤ t) (fun k => k + 1)

/-- Digit `i` of the `nd` digits of `t`, most significant first, as an ASCII byte. -/
def digitAt (t nd i : UInt64) : UInt64 := (t / pow10Word (nd - 1 - i)) % 10 + 0x30

/-- The `cnt` digits of the `nd` digits of `t` from digit `s`, most significant first, as ASCII
bytes. -/
def digitsFrom (t nd s cnt : UInt64) : Array UInt64 :=
  LeanExe.build cnt fun i => digitAt t nd (s + i)

/-- One byte. -/
def byte1 (b : UInt64) : Array UInt64 := LeanExe.build 1 fun _ => b

/-- No bytes. -/
def noBytes : Array UInt64 := LeanExe.build 0 fun _ => 0

/-- `n` zero digits. -/
def zeros (n : UInt64) : Array UInt64 := LeanExe.build n fun _ => 0x30

/-- The scientific layout of `(-1)^neg · t · 10^(kb - 2 ^ 62)` for `t ≥ 1`: the digits of `t`
with a point after the first when there are several, `e`, and the exponent of the first digit,
with `-` when it is negative. -/
def sciLayoutW (neg : Bool) (t kb : UInt64) : Array UInt64 :=
  let nd := numDigits t
  let xb := kb + nd - 1
  let xneg : Bool := xb < 0x4000000000000000
  let xa := if xneg then 0x4000000000000000 - xb else xb - 0x4000000000000000
  let nx := numDigits xa
  (if neg then byte1 0x2D else noBytes) ++ digitsFrom t nd 0 1 ++
    (if nd == 1 then noBytes else byte1 0x2E ++ digitsFrom t nd 1 (nd - 1)) ++ byte1 0x65 ++
    (if xneg then byte1 0x2D else noBytes) ++ digitsFrom xa nx 0 nx

/-- ECMA-262's Number::toString layout of `(-1)^neg · t · 10^(kb - 2 ^ 62)` for `t ≥ 1`, with the
point position `n = k + nd` biased as `nb`: plain digits and zeros for `nd ≤ n ≤ 21`, a point
inside the digits for `0 < n ≤ 21`, `0.` and zeros for `-6 < n ≤ 0`, and otherwise an exponent
with `+` or `-`. -/
def ecmaLayoutW (neg : Bool) (t kb : UInt64) : Array UInt64 :=
  let nd := numDigits t
  let nb := kb + nd
  let xpos : Bool := nb ≥ 0x4000000000000001
  let xa := if xpos then nb - 0x4000000000000001 else 0x4000000000000001 - nb
  let nx := numDigits xa
  (if neg then byte1 0x2D else noBytes) ++
    (if nb ≥ 0x4000000000000000 + nd && nb ≤ 0x4000000000000015 then
      digitsFrom t nd 0 nd ++ zeros (nb - 0x4000000000000000 - nd)
    else if nb > 0x4000000000000000 && nb ≤ 0x4000000000000015 then
      digitsFrom t nd 0 (nb - 0x4000000000000000) ++ byte1 0x2E ++
        digitsFrom t nd (nb - 0x4000000000000000) (nd - (nb - 0x4000000000000000))
    else if nb + 6 > 0x4000000000000000 && nb ≤ 0x4000000000000000 then
      byte1 0x30 ++ byte1 0x2E ++ zeros (0x4000000000000000 - nb) ++ digitsFrom t nd 0 nd
    else
      digitsFrom t nd 0 1 ++
        (if nd == 1 then noBytes else byte1 0x2E ++ digitsFrom t nd 1 (nd - 1)) ++ byte1 0x65 ++
        byte1 (if xpos then 0x2B else 0x2D) ++ digitsFrom xa nx 0 nx)

/-- The bytes of a fixed word, packed least significant first, as an array of `len` words. -/
def fixed (w len : UInt64) : Array UInt64 := LeanExe.build len fun i => (w >>> (8 * i)) &&& 0xFF

/-- `NaN`, `Infinity`, `-Infinity`, or the zero layout, for the non-finite and zero words of
sign `neg`, infinite when `inf`, and NaN when `nan`. -/
def special (neg inf nan ecma : Bool) : Array UInt64 :=
  if nan then fixed 0x4E614E 3
  else if inf then
    (if neg then LeanExe.build 9 fun i => if i == 0 then 0x2D else (0x7974696E69666E49 >>> (8 * (i - 1))) &&& 0xFF
     else fixed 0x7974696E69666E49 8)
  else if ecma then (if neg then fixed 0x302D 2 else fixed 0x30 1)
  else if neg then fixed 0x3065302D 4 else fixed 0x306530 3

/-- The decimal string of a binary64 word in the scientific layout. -/
def print64With (ecma : Bool) (w : UInt64) : Array UInt64 :=
  let neg := w >>> 63 == 1
  let ef := (w >>> 52) &&& 0x7FF
  let fr := w &&& 0xFFFFFFFFFFFFF
  if ef == 0x7FF then special neg true (fr != 0) ecma
  else if ef == 0 && fr == 0 then special neg false false ecma
  else
    let Q := if ef == 0 then fr else fr + 0x10000000000000
    let E := if ef == 0 then 1 else ef
    let s := shortest Q E 1074 (ef ≥ 2 && fr == 0)
    if ecma then ecmaLayoutW neg s.1 s.2 else sciLayoutW neg s.1 s.2

/-- The decimal string of a binary32 pattern in the low 32 bits of `w`. -/
def print32With (ecma : Bool) (w : UInt64) : Array UInt64 :=
  let x := w &&& 0xFFFFFFFF
  let neg := x >>> 31 == 1
  let ef := (x >>> 23) &&& 0xFF
  let fr := x &&& 0x7FFFFF
  if ef == 0xFF then special neg true (fr != 0) ecma
  else if ef == 0 && fr == 0 then special neg false false ecma
  else
    let Q := if ef == 0 then fr else fr + 0x800000
    let E := if ef == 0 then 1 else ef
    let s := shortest Q E 149 (ef ≥ 2 && fr == 0)
    if ecma then ecmaLayoutW neg s.1 s.2 else sciLayoutW neg s.1 s.2

/-- The shortest decimal string of a binary64 word, scientific layout: `1.5e3`, `5e-324`. -/
def print64 (w : UInt64) : Array UInt64 := print64With false w

/-- The shortest decimal string of a binary64 word in ECMA-262's layout: `1500`, `1.5e+21`. -/
def print64Ecma (w : UInt64) : Array UInt64 := print64With true w

/-- The shortest decimal string of the binary32 pattern in the low 32 bits of `w`. -/
def print32 (w : UInt64) : Array UInt64 := print32With false w

/-- The binary32 counterpart of `print64Ecma`. -/
def print32Ecma (w : UInt64) : Array UInt64 := print32With true w

end Library.Numerics.Decimal.PrintFloat.PrintFloat
