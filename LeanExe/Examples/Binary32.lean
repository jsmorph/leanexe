import LeanExe.Loop
import LeanExe.Build

namespace LeanExe.Examples.Binary32

/-- `a * x + y` in binary32, with two roundings. -/
def axpy32 (a x y : Float32) : Float32 := a * x + y

/-- The length of the vector `(x, y)` in binary32, with four roundings. -/
def hypot32 (x y : Float32) : Float32 := (x * x + y * y).sqrt

/-- `(a - b) / c` in binary32. -/
def ratio32 (a b c : Float32) : Float32 := (a - b) / c

/-- The product of the `rows × cols` matrix `m`, stored by rows, and the vector `v` in binary32,
with 0 for each missing element. -/
def matVec32 (m v : Array Float32) (rows cols : UInt64) : Array Float32 :=
  LeanExe.build rows fun r =>
    LeanExe.loop cols 0.0 fun c acc => acc + m[(r * cols + c).toNat]! * v[c.toNat]!

/-- `Piecewise.piecewise` in binary32: comparisons, conditionals, negation, absolute value, `min`,
and `max`. -/
def piecewise32 (x lo hi : Float32) : Float32 :=
  if x == lo then 0.0
  else if x < lo then -(lo - x) * 0.5
  else if hi ≤ x then (hi - x).abs + 1.5
  else max lo (min x hi)

/-- Each element of `x` times `a` in binary32. -/
def scale32 (a : Float32) (x : Array Float32) : Array Float32 :=
  LeanExe.build x.size.toUInt64 fun i => a * x[i.toNat]!

/-- `a * x + y` for each element in binary32, with 0 for each missing element of `y`. -/
def axpyArray32 (a : Float32) (x y : Array Float32) : Array Float32 :=
  LeanExe.build x.size.toUInt64 fun i => a * x[i.toNat]! + y[i.toNat]!

/-- Each element of `x`, replaced by its mirror within its group of four when below `lo` and the
mirror is below `n`, by `hi` when at least `hi`, and otherwise by the larger of `lo` and itself. -/
def condMix32 (x : Array Float32) (lo hi : Float32) (n : UInt64) : Array Float32 :=
  LeanExe.build x.size.toUInt64 fun i =>
    if x[i.toNat]! < lo then
      (if i % 4 ≤ 3 ∧ i / 4 * 4 + (3 - i % 4) < n then
        x[(i / 4 * 4 + (3 - i % 4)).toNat]!
      else max lo x[i.toNat]!)
    else if hi ≤ x[i.toNat]! then hi else max lo x[i.toNat]!

end LeanExe.Examples.Binary32
