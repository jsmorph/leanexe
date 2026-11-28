module

public import Demos.Scheme.Machine.Text

@[expose] public section

/-! The numeric layer of the executable interpreter.  Every numeric procedure and the reading of
numerals pass through this module, whose words are fixnums: the word of `8 n` for an integer `n`
from `-2^60` to `2^60 - 1`.  A later layer of integers of any size replaces these functions and
allocates objects of the reserved kind `K_BIGNUM`, and no caller changes.

An operation computes over `Int64`, whose 63 bits hold every sum and difference of two fixnums,
and checks the profile's range at its result.  A sum of many arguments keeps a two-word
accumulator, so a sum in the range is exact when a partial sum is not.  A product checks each step
for overflow by division and, after an overflow, returns 0 when a later factor is 0, since the
magnitude of a product of nonzero integers never decreases. -/

namespace Demos.Scheme.Machine.Numeric

open Demos.Scheme.Machine

/-- `2^60`, the magnitude of the least fixnum. -/
def LIMIT : UInt64 := 1152921504606846976

@[inline] def inRange (n : Int64) : Bool := -1152921504606846976 ≤ n && n ≤ 1152921504606846975

/-- The fixnum of an integer in `Int64`, or the restriction's status. -/
@[inline] def ofInt (n : Int64) : UInt64 × UInt64 :=
  if inRange n then (0, mkFix n) else (S_RESTRICTION + M_RANGE, 0)

/-! ## Numerals (§6.5.4) -/

/-- The value of the numeral from `p` to `e` of the source: the status 0 and a fixnum, the
restriction's status for a numeral outside the profile, or the read error of an invalid token,
whose offset is `p`.  The prefixes, the digits, and the bytes of numerals follow the reference
reader's `readNumeral`. -/
def readNumeral (src : LeanExe.Bytes) (p e : UInt64) : UInt64 × UInt64 :=
  -- prefixes: (offset, radix or 0, exactness: 0 none, 1 #e, 2 #i, bad)
  let pre := LeanExe.repeatWhile 4 (p, (0 : UInt64), (0 : UInt64), false)
    (fun s => !s.2.2.2 && s.1 + 1 < e && src.get s.1 == 35)
    fun s =>
      let k := foldByte (src.get (s.1 + 1))
      if k == 98 || k == 111 || k == 100 || k == 120 then
        if s.2.1 != 0 then (s.1, s.2.1, s.2.2.1, true)
        else (s.1 + 2, (if k == 98 then 2 else if k == 111 then 8 else if k == 100 then 10
          else 16), s.2.2.1, false)
      else if k == 101 || k == 105 then
        if s.2.2.1 != 0 then (s.1, s.2.1, s.2.2.1, true)
        else (s.1 + 2, s.2.1, (if k == 101 then 1 else 2), false)
      else (s.1, s.2.1, s.2.2.1, true)
  let q := pre.1
  let r := if pre.2.1 == 0 then 10 else pre.2.1
  let ex := pre.2.2.1
  let invalid : UInt64 × UInt64 := (S_READ + M_TOKEN, p)
  if pre.2.2.2 || q ≥ e then invalid
  else
    let c := src.get q
    let neg := c == 45
    let s := if c == 43 || c == 45 then q + 1 else q
    let digits := s < e && LeanExe.repeatWhile src.size s
      (fun i => i < e && digitValueB (src.get i) < r) (fun i => i + 1) == e
    if digits then
      if ex == 2 then (S_RESTRICTION + M_NUMBER, 0)
      else
        let mag := LeanExe.repeatWhile src.size (s, (0 : UInt64)) (fun st => st.1 < e)
          (fun st =>
            (st.1 + 1, if st.2 > LIMIT / r then LIMIT + LIMIT
              else st.2 * r + digitValueB (src.get st.1))) |>.2
        if neg then
          if mag ≤ LIMIT then (0, mkFix (0 - mag.toInt64)) else (S_RESTRICTION + M_RANGE, 0)
        else if mag < LIMIT then (0, mkFix mag.toInt64) else (S_RESTRICTION + M_RANGE, 0)
    else if allNumeral src r q e then (S_RESTRICTION + M_NUMBER, 0)
    else invalid

end Demos.Scheme.Machine.Numeric
