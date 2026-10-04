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

end LeanExe.Examples.Binary32
