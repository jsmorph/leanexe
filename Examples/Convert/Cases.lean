import Examples.Convert.Program
import Examples.Floor.Cases

/-! The inputs of the verified compiler's cases of `convert`.  The integers are the operands of the
floor cases and the integers that round at a tie or just past one: `2^53 + 1` and `2^53 + 3`, which
round to even in binary64 in opposite directions, `2^24 + 1` and `2^24 + 3` in binary32,
`2^62 + 2^38 + 1`, which rounds up in binary32 although its binary64 rounding is a tie, and
`2^63 - 1024` and `2^63 - 1025` beside the largest double below `2^63`, each with its negation.
The floats are given by their bits: the signed zeros, NaN, the infinities, values below 1 in
magnitude, `±2^63`, the largest float below `2^63` and its negation, the next float below `-2^63`,
the smallest subnormal, and large and small magnitudes of both signs. -/

namespace Examples.Convert

/-- The integers of the cases. -/
def ints : List Int64 :=
  Examples.Floor.samples ++
    [9007199254740993, 9007199254740995, 16777217, 16777219, 4611686293305294849,
      9223372036854774784, 9223372036854774783] ++
    [9007199254740993, 9007199254740995, 16777217, 16777219, 4611686293305294849,
      9223372036854774784, 9223372036854774783].map (fun x : Int64 => -x)

/-- The bits of the doubles of the cases. -/
def doubles : List UInt64 :=
  [0, 0x8000000000000000, 0x7FF8000000000000, 0x7FF0000000000000, 0xFFF0000000000000,
    0x3FE0000000000000, 0xBFE0000000000000, 0x3FF8000000000000, 0xBFF8000000000000,
    0x43E0000000000000, 0xC3E0000000000000, 0x43DFFFFFFFFFFFFF, 0xC3DFFFFFFFFFFFFF,
    0xC3E0000000000001, 0x43E0000000000001, 0x0000000000000001, 0x8000000000000001,
    0x7E37E43C8800759C, 0xFE37E43C8800759C, 0x4340000000000001, 0xC340000000000001,
    0x400921FB54442D18, 0xC00921FB54442D18]

/-- The bits of the singles of the cases. -/
def singles : List UInt32 :=
  [0, 0x80000000, 0x7FC00000, 0x7F800000, 0xFF800000, 0x3F000000, 0xBF000000, 0x3FC00000,
    0xBFC00000, 0x5F000000, 0xDF000000, 0x5EFFFFFF, 0xDEFFFFFF, 0xDF000001, 0x5F000001,
    0x00000001, 0x80000001, 0x7F7FFFFF, 0xFF7FFFFF, 0x4B800001, 0xCB800001]

/-- The bits of the gains of `scale`'s cases: 0.5, -1.5, 3, `2^-1074`, `10^300`, -0, NaN, and
infinity. -/
def gains : List UInt64 :=
  [0x3FE0000000000000, 0xBFF8000000000000, 0x4008000000000000, 0x0000000000000001,
    0x7E37E43C8800759C, 0x8000000000000000, 0x7FF8000000000000, 0x7FF0000000000000]

end Examples.Convert
