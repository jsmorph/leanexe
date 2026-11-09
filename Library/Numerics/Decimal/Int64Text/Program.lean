import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop

/-!
The decimal printer and reader of `Int64`, on texts of one byte to a word.  `printInt64` writes the
magnitude's digits from the most significant, digit `k` from the least significant being
`m / 10^k % 10`, after `-` for a negative value.  The magnitude of `minValue` is `2^63`, which the
word `0 - x.toUInt64` holds.  `readInt64` reads an optional `-` and at most 19 digits, whose value
is below `10^19 < 2^64` and so needs no test of overflow, and compares the value with `2^63 - 1`,
or with `2^63` after `-`.  A text with more digits and no leading zero is at least `10^19`, outside
the range, so the reader rejects it without reading it.
-/

namespace Library.Numerics.Decimal.Int64Text

/-- The number of decimal digits of `m`, 1 for 0: the count of the divisions by 10 that leave a
nonzero quotient, plus 1, for at most 19 divisions. -/
def digitCount (m : UInt64) : UInt64 :=
  (LeanExe.loop 19 ((1 : UInt64), m / 10) fun _ s =>
    if s.2 != 0 then (s.1 + 1, s.2 / 10) else s).1

/-- The byte of digit `k` of `m`, counted from the least significant. -/
def digitByte (m k : UInt64) : UInt64 :=
  (LeanExe.loop k m fun _ q => q / 10) % 10 + 48

/-- The decimal text of `x`. -/
def printInt64 (x : Int64) : Array UInt64 :=
  let sign : UInt64 := if x < 0 then 1 else 0
  let m : UInt64 := if x < 0 then 0 - x.toUInt64 else x.toUInt64
  let len := digitCount m
  LeanExe.build (len + sign) fun i =>
    if i < sign then 45 else digitByte m (len + sign - 1 - i)

/-- Whether the word `w` holds a decimal digit. -/
def isDigitW (w : UInt64) : Bool := 48 ≤ w && w ≤ 57

/-- Whether the `count` words of `s` from `start` are digits, and their value as a decimal
numeral, modulo `2^64`. -/
def scanDigits (s : Array UInt64) (start count : UInt64) : Bool × UInt64 :=
  LeanExe.loop count (true, (0 : UInt64)) fun i st =>
    let w := s[(start + i).toNat]!
    (st.1 && isDigitW w, 10 * st.2 + (w - 48))

/-- The value of the text `s` with the flag `true`, or `(false, 0)` when `s` is not the text of
an `Int64`. -/
def readInt64 (s : Array UInt64) : Bool × Int64 :=
  let n := s.size.toUInt64
  if n == 0 then (false, 0)
  else
    let neg := s[(0 : UInt64).toNat]! == 45
    let start : UInt64 := if neg then 1 else 0
    let count := n - start
    if count == 0 || count > 19 then (false, 0)
    else
      let r := scanDigits s start count
      let first := s[start.toNat]!
      let limit : UInt64 := if neg then 9223372036854775808 else 9223372036854775807
      if r.1 && (first != 48 || (count == 1 && !neg)) && r.2 ≤ limit then
        (true, if neg then (0 - r.2).toInt64 else r.2.toInt64)
      else (false, 0)

end Library.Numerics.Decimal.Int64Text
