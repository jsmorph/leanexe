module

public import LeanExe.Dialect.Loop
public import LeanExe.Dialect.Build
public import Library.Numerics.MultiPrecision.Program
public import Library.Numerics.Decimal.Int64Text.Program
public import Library.Numerics.Bignum.Types

@[expose] public section

/-!
Arbitrary-precision naturals and integers in leanexe's verified dialect.  A natural is an array of
limbs below `2^32`, least significant first, with no zero limb at the top, and an integer is a
`BigInt`, a sign and such a magnitude, with zero never negative.  The functions take arguments of
this form and return results of it.

The natural functions apply MultiPrecision's Algorithms A, S, M, and D and trim the result with
`natTrim`, which copies the limbs below `significant`.  Comparison applies Uscale's `le` in both
orders.  The integer functions choose signs and call the natural functions on the magnitudes.

`intToText` divides a working copy of the magnitude by `10^9` in place, `K = n + n / 14 + 2` times
for `n` limbs, and keeps each remainder, a chunk of nine decimal digits, in an array that it
updates in place.  `10^(9 K) > 2^(32 n)`, so the chunks hold every digit.  The text is the sign,
the digits of the top nonzero chunk, and nine digits of each chunk below it, each written with
Int64Text's `digitByte`.  `intOfText` checks Int64Text's grammar, and reads the digits in chunks
of nine, padded with leading zeros to a multiple of nine, into an array of `C = ⌈D / 9⌉` limbs for
`D` digits, which it multiplies by `10^9` and adds to in place.  `10^(9 C) < 2^(32 C)`, so the
limbs hold the value.  Each update in place writes an owned array in a loop's state, so the
allocation of each text function is linear in the length of its argument.

The exports with `Checked` and `text` in their names return the error statuses of `Spec.lean`.
The helpers marked `@[inline]`, among them the divisions of Lean's convention, are not compiled as
functions of their own: the verified compiler expands them into their callers, so the module does
not export them.
-/

namespace Library.Numerics.Bignum

open Library.Numerics.MultiPrecision (significant add sub mul divide)
open Library.Numerics.Decimal.Int64Text (digitCount digitByte isDigitW)

/-! ## Naturals -/

/-- The limbs of `u` below its top nonzero limb. -/
def natTrim (u : Array UInt64) : Array UInt64 :=
  LeanExe.build (significant u) fun i => u[i.toNat]!

/-- 0, 1, or 2 when `u` is less than, equal to, or greater than `v`. -/
def natCmp (u v : Array UInt64) : UInt64 :=
  if Library.Numerics.Arithmetic.Uscale.le u v then
    (if Library.Numerics.Arithmetic.Uscale.le v u then 1 else 0)
  else 2

def natAdd (u v : Array UInt64) : Array UInt64 := natTrim (add u v)

/-- Whether `u < v`, and the difference of the larger and the smaller. -/
def natSub (u v : Array UInt64) : Bool × Array UInt64 :=
  if Library.Numerics.Arithmetic.Uscale.le v u then (false, natTrim (sub u v))
  else (true, natTrim (sub v u))

def natMul (u v : Array UInt64) : Array UInt64 := natTrim (mul u v)

/-- The `len` words of `w` from position `start`. -/
@[inline] def slice (w : Array UInt64) (start len : UInt64) : Array UInt64 :=
  LeanExe.build len fun i => w[(start + i).toNat]!

/-- The quotient and the remainder, with `u / 0 = 0` and `u % 0 = u`.  `divide` returns the
`m` digits of the quotient followed by the `n` digits of the remainder. -/
@[inline] def natDivMod (u v : Array UInt64) : Array UInt64 × Array UInt64 :=
  if v.size.toUInt64 == 0 then (#[], natTrim u)
  else
    let r := divide u v
    (natTrim (slice r 0 u.size.toUInt64), natTrim (slice r u.size.toUInt64 v.size.toUInt64))

/-- The status 1 and two zeros for a zero divisor, and otherwise the status 0, the quotient, and
the remainder. -/
def natDivModChecked (u v : Array UInt64) : UInt64 × Array UInt64 × Array UInt64 :=
  if v.size.toUInt64 == 0 then (1, #[], #[])
  else
    let qr := natDivMod u v
    (0, qr.1, qr.2)

/-! ## Integers -/

def intNeg (x : BigInt) : BigInt := ⟨!x.neg && x.mag.size.toUInt64 != 0, natTrim x.mag⟩

def intCmp (x y : BigInt) : UInt64 :=
  if x.neg then (if y.neg then natCmp y.mag x.mag else 0)
  else (if y.neg then 2 else natCmp x.mag y.mag)

/-- The sum of the integers of the signs `xn` and `yn` and the magnitudes `xm` and `ym`. -/
@[inline] def addCore (xn : Bool) (xm : Array UInt64) (yn : Bool) (ym : Array UInt64) : BigInt :=
  if xn == yn then ⟨xn, natAdd xm ym⟩
  else
    let d := natSub xm ym
    ⟨(if d.1 then yn else xn) && d.2.size.toUInt64 != 0, d.2⟩

def intAdd (x y : BigInt) : BigInt := addCore x.neg x.mag y.neg y.mag

def intSub (x y : BigInt) : BigInt := addCore x.neg x.mag (!y.neg) y.mag

def intMul (x y : BigInt) : BigInt :=
  let p := natMul x.mag y.mag
  ⟨(x.neg != y.neg) && p.size.toUInt64 != 0, p⟩

/-- The truncated quotient and remainder: the quotient's sign from both signs, the remainder's
from the dividend's. -/
@[inline] def intTDivMod (x y : BigInt) : BigInt × BigInt :=
  let qr := natDivMod x.mag y.mag
  (⟨(x.neg != y.neg) && qr.1.size.toUInt64 != 0, qr.1⟩, ⟨x.neg && qr.2.size.toUInt64 != 0, qr.2⟩)

/-- Lean's Euclidean quotient and remainder: the truncated ones, corrected when the remainder is
negative and the divisor is not 0, by one step of the quotient away from zero and the remainder
`|y| - |r|`. -/
@[inline] def intEDivMod (x y : BigInt) : BigInt × BigInt :=
  let t := intTDivMod x y
  if t.2.neg && y.mag.size.toUInt64 != 0 then
    (⟨!y.neg, natAdd t.1.mag #[1]⟩, ⟨false, (natSub y.mag t.2.mag).2⟩)
  else t

def intTDivModChecked (x y : BigInt) : UInt64 × BigInt × BigInt :=
  if y.mag.size.toUInt64 == 0 then (1, ⟨false, #[]⟩, ⟨false, #[]⟩)
  else
    let t := intTDivMod x y
    (0, t.1, t.2)

def intEDivModChecked (x y : BigInt) : UInt64 × BigInt × BigInt :=
  if y.mag.size.toUInt64 == 0 then (1, ⟨false, #[]⟩, ⟨false, #[]⟩)
  else
    let t := intEDivMod x y
    (0, t.1, t.2)

/-! ## Text -/

/-- The `K` chunks of nine decimal digits of the value of `m`, least significant first: a working
copy of `m` divided by `10^9` in place, from its top limb down, `K` times, with each remainder
written to the chunk array in place. -/
@[inline] def chunks (m : Array UInt64) (K : UInt64) : Array UInt64 :=
  let n := m.size.toUInt64
  (LeanExe.loop K (LeanExe.build n (fun i => m[i.toNat]!), LeanExe.build K fun _ => (0 : UInt64))
    fun k st =>
      let s := LeanExe.loop n ((0 : UInt64), st.1) fun e s =>
        ((s.1 * 4294967296 + s.2[(n - 1 - e).toNat]!) % 1000000000,
          s.2.set! (n - 1 - e).toNat ((s.1 * 4294967296 + s.2[(n - 1 - e).toNat]!) / 1000000000))
      (s.2, st.2.set! k.toNat s.1)).2

/-- The decimal text of `x`: `-` for a negative sign, the digits of the top nonzero chunk, and
nine digits of each chunk below it.  Position `p` from the least significant digit is digit
`p % 9` of chunk `p / 9`. -/
def intToText (x : BigInt) : Array UInt64 :=
  let n := x.mag.size.toUInt64
  let c := chunks x.mag (n + n / 14 + 2)
  let sc := significant c
  let t := if sc == 0 then 0 else sc - 1
  let sign : UInt64 := if x.neg then 1 else 0
  let len := sign + digitCount c[t.toNat]! + 9 * t
  LeanExe.build len fun i =>
    if i < sign then 45 else digitByte c[((len - 1 - i) / 9).toNat]! ((len - 1 - i) % 9)

/-- Whether the `count` words of `s` from `start` are decimal digits. -/
@[inline] def allDigits (s : Array UInt64) (start count : UInt64) : Bool :=
  LeanExe.loop count true fun i ok => ok && isDigitW s[(start + i).toNat]!

/-- The canonical limbs of the value of the `count` decimal digits of `s` from `start`.  The
digits, padded with `pad` leading zeros to `9 C` digits, form `C` chunks of nine, and each chunk
multiplies the limbs by `10^9` and adds its value, in place over all `C` limbs. -/
@[inline] def decimalValue (s : Array UInt64) (start count : UInt64) : Array UInt64 :=
  let C := (count + 8) / 9
  let pad := 9 * C - count
  natTrim (LeanExe.loop C (LeanExe.build C fun _ => (0 : UInt64)) fun k w =>
    let d := LeanExe.loop 9 (0 : UInt64) fun e v =>
      10 * v + (if 9 * k + e < pad then 0 else s[(start + (9 * k + e - pad)).toNat]! - 48)
    (LeanExe.loop C (d, w) fun i st =>
      ((st.2[i.toNat]! * 1000000000 + st.1) >>> 32,
        st.2.set! i.toNat ((st.2[i.toNat]! * 1000000000 + st.1) &&& 0xFFFFFFFF))).2)

/-- `(true, x)` for a text of the grammar `"0" / ["-"] nonzero *digit` that denotes `x`, and
`(false, 0)` otherwise. -/
def intOfText (s : Array UInt64) : Bool × BigInt :=
  let n := s.size.toUInt64
  if n == 0 then (false, ⟨false, #[]⟩)
  else
    let neg := s[(0 : UInt64).toNat]! == 45
    let start : UInt64 := if neg then 1 else 0
    let count := n - start
    if count == 0 then (false, ⟨false, #[]⟩)
    else if allDigits s start count && (s[start.toNat]! != 48 || (count == 1 && !neg)) then
      (true, ⟨neg, decimalValue s start count⟩)
    else (false, ⟨false, #[]⟩)

/-! ## Text exports -/

def textNeg (s : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then (0, intToText (intNeg a.2)) else (1, #[])

def textCmp (s t : Array UInt64) : UInt64 × UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then (0, intCmp a.2 b.2) else (2, 0)
  else (1, 0)

def textAdd (s t : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then (0, intToText (intAdd a.2 b.2)) else (2, #[])
  else (1, #[])

def textSub (s t : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then (0, intToText (intSub a.2 b.2)) else (2, #[])
  else (1, #[])

def textMul (s t : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then (0, intToText (intMul a.2 b.2)) else (2, #[])
  else (1, #[])

def textTDiv (s t : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then
      (if b.2.mag.size.toUInt64 == 0 then (3, #[]) else (0, intToText (intTDivMod a.2 b.2).1))
    else (2, #[])
  else (1, #[])

def textTMod (s t : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then
      (if b.2.mag.size.toUInt64 == 0 then (3, #[]) else (0, intToText (intTDivMod a.2 b.2).2))
    else (2, #[])
  else (1, #[])

def textEDiv (s t : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then
      (if b.2.mag.size.toUInt64 == 0 then (3, #[]) else (0, intToText (intEDivMod a.2 b.2).1))
    else (2, #[])
  else (1, #[])

def textEMod (s t : Array UInt64) : UInt64 × Array UInt64 :=
  let a := intOfText s
  if a.1 then
    let b := intOfText t
    if b.1 then
      (if b.2.mag.size.toUInt64 == 0 then (3, #[]) else (0, intToText (intEDivMod a.2 b.2).2))
    else (2, #[])
  else (1, #[])

end Library.Numerics.Bignum
