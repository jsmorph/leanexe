import LeanExe.Loop
import LeanExe.Build

namespace LeanExe.Examples.Gpt

/-- The dot product of `xs` and `ys` over the length of `xs`, with 0 for each
missing element of `ys`. -/
def dot (xs ys : Array Float) : Float :=
  LeanExe.loop xs.size.toUInt64 0.0 fun i acc => acc + xs[i.toNat]! * ys[i.toNat]!

/-- The product of the `rows × cols` matrix `m`, stored by rows, and the vector
`v`, with 0 for each missing element. -/
def matVec (m v : Array Float) (rows cols : UInt64) : Array Float :=
  LeanExe.build rows fun r =>
    LeanExe.loop cols 0.0 fun c acc => acc + m[(r * cols + c).toNat]! * v[c.toNat]!

/-- The layer normalization of `xs` with gain `g` and bias `b`, with `eps` added to
the variance and 0 for each missing gain or bias. -/
def layerNorm (xs g b : Array Float) (eps : Float) : Array Float :=
  let n := xs.size.toUInt64.toFloat
  let mean := LeanExe.loop xs.size.toUInt64 0.0 (fun i acc => acc + xs[i.toNat]!) / n
  let var := LeanExe.loop xs.size.toUInt64 0.0
    (fun i acc => acc + (xs[i.toNat]! - mean) * (xs[i.toNat]! - mean)) / n
  let inv := 1.0 / (var + eps).sqrt
  LeanExe.build xs.size.toUInt64 fun i => (xs[i.toNat]! - mean) * inv * g[i.toNat]! + b[i.toNat]!

end LeanExe.Examples.Gpt
