import LeanExe.Dialect.Loop

namespace Library.Numerics.Arithmetic.CeilSqrt

/-- The least `r` with `n ≤ r * r`, for `n ≤ 2^32`, by 17 halvings of the bracket
`[0, 65536]`. -/
def ceilSqrt (n : UInt64) : UInt64 :=
  match LeanExe.loop 17 ((0 : UInt64), (65536 : UInt64)) fun _ bracket =>
      let mid := (bracket.1 + bracket.2) / 2
      (if bracket.1 < bracket.2 && mid * mid < n then mid + 1 else bracket.1,
        if bracket.1 < bracket.2 && n ≤ mid * mid then mid else bracket.2) with
  | (lo, _) => lo

end Library.Numerics.Arithmetic.CeilSqrt
