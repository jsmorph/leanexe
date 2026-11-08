import Examples.Floor.Program

/-! The inputs of the verified compiler's cases of `floor`: the extremes of `Int64`, the values
near 0, and odd and even values of both signs, in every pair. -/

namespace Examples.Floor

/-- The operands of the cases. -/
def samples : List Int64 :=
  [Int64.minValue, Int64.minValue + 1, -1000000007, -8, -7, -2, -1, 0, 1, 2, 7, 8, 1000000007,
    Int64.maxValue - 1, Int64.maxValue]

end Examples.Floor
