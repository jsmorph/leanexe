import Library.Numerics.Decimal.Int64Text.Spec
import TestSupport.Host

/-! The inputs of the verified compiler's cases of the `Int64` decimal printer and reader. -/

namespace Library.Numerics.Decimal.Int64Text

/-- The words of the characters of an ASCII string. -/
def text (s : String) : List UInt64 := s.toList.map fun c => c.toNat.toUInt64

/-- The values that the cases print: 0, ±1, ±7, ±9, ±42, ±12345, the largest and smallest
values and their neighbors, each power of ten from `10` to `10^18` with its neighbor toward zero
and both negated, each power of two from `2^0` to `2^62` and its negation, and 40 arbitrary words
read as `Int64`. -/
def printInputs : List Int64 :=
  let tens := (List.range 18).flatMap fun k =>
    let p := Int64.ofInt (10 ^ (k + 1))
    [p, p - 1, -p, 1 - p]
  let twos := (List.range 63).flatMap fun k =>
    let p := Int64.ofInt (2 ^ k)
    [p, -p]
  [0, 1, -1, 7, -7, 9, -9, 42, -42, 12345, -12345, Int64.maxValue, Int64.maxValue - 1,
    Int64.minValue, Int64.minValue + 1] ++ tens ++ twos ++
    (List.range 40).map fun i => (TestSupport.Host.rw i).toInt64

/-- The arrays that the cases read.  The texts cover the empty array, `0`, `-0`, a lone sign,
signs `+` and `-` first, after a sign, inside the digits, and after them, leading zeros, a space,
a tab, a carriage return, a line feed, a vertical tab, and a form feed before or after the digits,
a space and a line feed inside them, other bytes before, inside, and after the digits, a decimal
point and an exponent, the largest and smallest values, their neighbors inside and outside the
range, nineteen nines, `10^18` and `10^19`, `2^64 - 1`, `2^64`, and `2^64 + 1` with and without
`-`, some of which a reader that wraps modulo `2^64` would accept, `2^65 + 1`, 20-digit values from
`2.05 · 10^19` to `2.7 · 10^19` with and without `-`, whose accumulation in 64 bits wraps to a
larger word in range, and texts of 21, 31, and 42 bytes.  The word arrays cover the bytes from
128 to 255 whose low 7 bits are a digit or `-`, alone, and some of them after a digit or a sign or
before a digit, the bytes 128 and 255, alone and after a digit or a sign, words above 255 whose low
byte is a digit or `-`, the words 0, 47, 58, and `2^64 - 1`, a digit followed by the word 0, and
1,000 words of `1`.  The texts of the printed values of `printInputs` follow. -/
def readInputs : List (List UInt64) :=
  let texts := ["", "0", "-0", "+0", "+5", "+", "-", "--5", "-+5", "+-5", "00", "05", "-05",
    "007", "000", "-00", "5-", "1-2", "12-", "1a", "a1", " 1", "1 ", "1\n", "-\n1", "\n", "1.0",
    "1e3", "0x10", "1", "-1", "9", "-9", "10", "-10", "12345", "-12345", "1234567890123456789",
    "-1234567890123456789", "9223372036854775807", "9223372036854775806",
    "9223372036854775808", "9223372036854775809", "-9223372036854775808",
    "-9223372036854775807", "-9223372036854775809", "-9223372036854775810",
    "09223372036854775807", "-09223372036854775808", "9999999999999999999",
    "-9999999999999999999", "1000000000000000000", "-1000000000000000000",
    "10000000000000000000", "-10000000000000000000", "18446744073709551615",
    "18446744073709551616", "18446744073709551617", "-18446744073709551617",
    "-18446744073709551616", "36893488147419103233", "99999999999999999999",
    "123456789012345678901", "1000000000000000000000000000000",
    "-10000000000000000000000000000000000000000", "00000000000000000000001", "5+", "1+2",
    "25000000000000000000", "-25000000000000000000", "20500000000000000000",
    "27000000000000000000", "-27000000000000000000", "-20500000000000000000",
    "-18446744073709551615", "1 2", "1\n2", "\t1", "1\t", "\r1", "1\r", "\x0b1", "1\x0c"]
  let arrays : List (List UInt64) :=
    [[0xAD]] ++ (List.range 10).map (fun k => [UInt64.ofNat (0xB0 + k)]) ++
    [[0xAD, 0x31], [0x31, 0xB0], [45, 0xB1], [0x80], [0xFF], [49, 0xFF], [45, 0x80], [304],
      [49, 304], [301, 49], [0x8000000000000031], [0x100000030], [0xFFFFFFFFFFFFFFFF], [0], [47],
      [58], [48, 0], [49, 0], [0, 49], [45, 0], [45, 304], [0x12D, 0x131],
      List.replicate 1000 49]
  texts.map text ++ arrays ++ printInputs.map fun x => (expectedPrint x).toList

end Library.Numerics.Decimal.Int64Text
