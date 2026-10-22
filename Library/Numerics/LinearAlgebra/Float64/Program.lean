import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

namespace Library.Numerics.LinearAlgebra.Float64

/-- The dot product over the indices of `xs`, with `ys` read as 0 past its end. -/
def dot (xs ys : Array Float) : Float :=
  LeanExe.loop xs.size.toUInt64 0.0 fun i acc => acc + xs[i.toNat]! * ys[i.toNat]!

/-- `a * x + y` for each element of `ys`, written in place. -/
def axpy (a : Float) (xs ys : Array Float) : Array Float :=
  LeanExe.loop ys.size.toUInt64 ys fun i acc =>
    acc.set! i.toNat (a * xs[i.toNat]! + acc[i.toNat]!)

/-- The points of a grid from `x0` with step `dx`. -/
def grid (n : UInt64) (x0 dx : Float) : Array Float :=
  LeanExe.build n fun i => x0 + i.toFloat * dx

/-- The product of the `rows × cols` matrix `m`, stored by rows, and the vector
`v`, with 0 for each missing element. -/
def matVec (m v : Array Float) (rows cols : UInt64) : Array Float :=
  LeanExe.build rows fun r =>
    LeanExe.loop cols 0.0 fun c acc => acc + m[(r * cols + c).toNat]! * v[c.toNat]!

/-- The product of the `n × k` matrix `a` and the `k × m` matrix `b`, both stored by
rows, as an `n × m` matrix stored by rows, with 0 for each missing element. -/
def matMul (a b : Array Float) (n k m : UInt64) : Array Float :=
  LeanExe.build (n * m) fun e =>
    LeanExe.loop k 0.0 fun c acc => acc + a[(e / m * k + c).toNat]! * b[(c * m + e % m).toNat]!

/-- The product of the `n × k` matrix `a` and the transpose of the `m × k` matrix
`b`, both stored by rows, as an `n × m` matrix stored by rows. -/
def matMulT (a b : Array Float) (n k m : UInt64) : Array Float :=
  LeanExe.build (n * m) fun e =>
    LeanExe.loop k 0.0 fun c acc => acc + a[(e / m * k + c).toNat]! * b[(e % m * k + c).toNat]!

/-- The element-wise sum of `a` and `b` over the length of `a`, with 0 for each
missing element of `b`. -/
def add (a b : Array Float) : Array Float :=
  LeanExe.build a.size.toUInt64 fun i => a[i.toNat]! + b[i.toNat]!

end Library.Numerics.LinearAlgebra.Float64
