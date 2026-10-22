import Library.Numerics.LinearAlgebra.Binary32.Program
import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

namespace Examples.Binary32

export Library.Numerics.LinearAlgebra.Binary32 (scale32 axpyArray32 matVec32)

/-- `a * x + y` in binary32, with two roundings. -/
def axpy32 (a x y : Float32) : Float32 := a * x + y

/-- The length of the vector `(x, y)` in binary32, with four roundings. -/
def hypot32 (x y : Float32) : Float32 := (x * x + y * y).sqrt

/-- `(a - b) / c` in binary32. -/
def ratio32 (a b c : Float32) : Float32 := (a - b) / c

/-- `Piecewise.piecewise` in binary32: comparisons, conditionals, negation, absolute value, `min`,
and `max`. -/
def piecewise32 (x lo hi : Float32) : Float32 :=
  if x == lo then 0.0
  else if x < lo then -(lo - x) * 0.5
  else if hi ≤ x then (hi - x).abs + 1.5
  else max lo (min x hi)

/-- Each element of `x`, replaced by its mirror within its group of four when below `lo` and the
mirror is below `n`, by `hi` when at least `hi`, and otherwise by the larger of `lo` and itself. -/
def condMix32 (x : Array Float32) (lo hi : Float32) (n : UInt64) : Array Float32 :=
  LeanExe.build x.size.toUInt64 fun i =>
    if x[i.toNat]! < lo then
      (if i % 4 ≤ 3 ∧ i / 4 * 4 + (3 - i % 4) < n then
        x[(i / 4 * 4 + (3 - i % 4)).toNat]!
      else max lo x[i.toNat]!)
    else if hi ≤ x[i.toNat]! then hi else max lo x[i.toNat]!

end Examples.Binary32
