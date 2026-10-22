import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

namespace Library.Numerics.LinearAlgebra.Binary32

/-- Each element of `x` times `a` in binary32. -/
def scale32 (a : Float32) (x : Array Float32) : Array Float32 :=
  LeanExe.build x.size.toUInt64 fun i => a * x[i.toNat]!

/-- `a * x + y` for each element in binary32, with 0 for each missing element of `y`. -/
def axpyArray32 (a : Float32) (x y : Array Float32) : Array Float32 :=
  LeanExe.build x.size.toUInt64 fun i => a * x[i.toNat]! + y[i.toNat]!

/-- The product of the `rows × cols` matrix `m`, stored by rows, and the vector `v` in binary32,
with 0 for each missing element. -/
def matVec32 (m v : Array Float32) (rows cols : UInt64) : Array Float32 :=
  LeanExe.build rows fun r =>
    LeanExe.loop cols 0.0 fun c acc => acc + m[(r * cols + c).toNat]! * v[c.toNat]!

/-- The element-wise sum of `a` and `b`. -/
def add32 (a b : Array Float32) : Array Float32 :=
  LeanExe.build a.size.toUInt64 fun i => a[i.toNat]! + b[i.toNat]!

/-- The row `x` of `k` elements times the `k × m` matrix `w`, stored by rows, plus the bias
`b`. -/
def linear32 (x w b : Array Float32) (k m : UInt64) : Array Float32 :=
  LeanExe.build m fun c =>
    LeanExe.loop k 0.0 (fun i acc => acc + x[i.toNat]! * w[(i * m + c).toNat]!) + b[c.toNat]!

end Library.Numerics.LinearAlgebra.Binary32
