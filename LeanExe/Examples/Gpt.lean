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

/-- `e^x` in binary64.  It writes `x = k·ln 2 + r` with `k` an integer and `|r|` at
most about `ln 2 / 2`, evaluates the Taylor polynomial of degree 13 for `e^r`, and
multiplies by `2^k` as a product of two powers of two built from their bits.  NaN
yields `x`, values above 709.8 yield infinity, and values below -745.2 yield 0.
Tests compare it with the C library's `exp`; no theorem bounds its error. -/
def exp (x : Float) : Float :=
  let c := max (-745.2) (min x 709.8)
  let m := (c * 1.4426950408889634 + 1100.5).toUInt64
  let kf := m.toFloat - 1100.0
  let r := c - kf * 0.6931471803691238 - kf * 1.9082149292705877e-10
  let p := 1.0 + r * (1.0 + r * (0.5 + r * (0.16666666666666666 + r * (0.041666666666666664 +
    r * (0.008333333333333333 + r * (0.001388888888888889 + r * (1.984126984126984e-4 +
    r * (2.48015873015873e-5 + r * (2.7557319223985893e-6 + r * (2.755731922398589e-7 +
    r * (2.505210838544172e-8 + r * (2.08767569878681e-9 + r * 1.6059043836821613e-10))))))))))))
  let h := m / 2
  let y := p * Float.ofBits ((h + 473) <<< 52) * Float.ofBits ((m - h + 473) <<< 52)
  if x == x then (if x > 709.8 then x * 1e308 else if x < -745.2 then 0.0 else y) else x

/-- The softmax of `xs`: `exp (xs[i] - m)` divided by the sum of these values, where
`m` is the largest element. -/
def softmax (xs : Array Float) : Array Float :=
  let mx := LeanExe.loop xs.size.toUInt64 (-(1.0 / 0.0)) fun i acc => max acc xs[i.toNat]!
  let total := LeanExe.loop xs.size.toUInt64 0.0 fun i acc => acc + exp (xs[i.toNat]! - mx)
  LeanExe.build xs.size.toUInt64 fun i => exp (xs[i.toNat]! - mx) / total

/-- Two matrix-vector products, `w2 · (w1 · x)`, where `w1` has `hidden` rows and
`d` columns and `w2` has `d` rows and `hidden` columns.  The intermediate vector
is a temporary array. -/
def matVec2 (w1 w2 x : Array Float) (hidden d : UInt64) : Array Float :=
  let h := matVec w1 x hidden d
  matVec w2 h d hidden

/-- The product of the `n × k` matrix `a` and the `k × m` matrix `b`, both stored by
rows, as an `n × m` matrix stored by rows, with 0 for each missing element. -/
def matMul (a b : Array Float) (n k m : UInt64) : Array Float :=
  LeanExe.build (n * m) fun e =>
    LeanExe.loop k 0.0 fun c acc => acc + a[(e / m * k + c).toNat]! * b[(c * m + e % m).toNat]!

/-- The element-wise sum of `a` and `b` over the length of `a`, with 0 for each
missing element of `b`. -/
def add (a b : Array Float) : Array Float :=
  LeanExe.build a.size.toUInt64 fun i => a[i.toNat]! + b[i.toNat]!

/-- `tanh z` as `1 - 2 / (e^(2z) + 1)`, which gives 1 and -1 at the two ends of the
range.  Near 0 it loses relative accuracy through cancellation. -/
def tanh (z : Float) : Float := 1.0 - 2.0 / (exp (2.0 * z) + 1.0)

/-- GPT-2's GELU: `0.5 x (1 + tanh (√(2/π) (x + 0.044715 x³)))`. -/
def gelu (x : Float) : Float :=
  let u := 0.7978845608028654 * (x + 0.044715 * x * x * x)
  0.5 * x * (1.0 + tanh u)

/-- `gelu` applied to each element of `xs`. -/
def geluArray (xs : Array Float) : Array Float :=
  LeanExe.build xs.size.toUInt64 fun i => gelu xs[i.toNat]!

/-- The MLP of a transformer block on `t` rows of width `d` with hidden width `f`:
`gelu (x · w1) · w2`, where `x` is `t × d`, `w1` is `d × f`, and `w2` is `f × d`. -/
def mlp (x w1 w2 : Array Float) (t d f : UInt64) : Array Float :=
  let h := matMul x w1 t d f
  let g := geluArray h
  matMul g w2 t f d

/-- The mean of each of the `t` rows of width `d` of `x`. -/
def rowMeans (x : Array Float) (t d : UInt64) : Array Float :=
  LeanExe.build t fun r =>
    LeanExe.loop d 0.0 (fun c acc => acc + x[(r * d + c).toNat]!) / d.toFloat

/-- `1 / √(variance + eps)` of each of the `t` rows of width `d` of `x`, given the
row means. -/
def rowInvStd (x means : Array Float) (t d : UInt64) (eps : Float) : Array Float :=
  LeanExe.build t fun r =>
    1.0 / (LeanExe.loop d 0.0 (fun c acc =>
      acc + (x[(r * d + c).toNat]! - means[r.toNat]!) * (x[(r * d + c).toNat]! - means[r.toNat]!)) /
        d.toFloat + eps).sqrt

/-- Each of the `t` rows of width `d` of `x`, normalized with the row means and
inverse deviations, then scaled by `g` and shifted by `b`. -/
def normalizeRows (x means invStd g b : Array Float) (t d : UInt64) : Array Float :=
  LeanExe.build (t * d) fun e =>
    (x[e.toNat]! - means[(e / d).toNat]!) * invStd[(e / d).toNat]! * g[(e % d).toNat]! +
      b[(e % d).toNat]!

/-- The layer normalization of each of the `t` rows of width `d` of `x`. -/
def layerNormRows (x g b : Array Float) (t d : UInt64) (eps : Float) : Array Float :=
  let means := rowMeans x t d
  let inv := rowInvStd x means t d eps
  normalizeRows x means inv g b t d

/-- The causally masked attention scores of `t` queries and keys of width `d`, both
stored by rows, as a `t × t` matrix stored by rows: `scale · (q[i] · k[j])` plus a
mask that is 0 where `j ≤ i` and negative infinity elsewhere. -/
def maskedScores (q k : Array Float) (t d : UInt64) (scale : Float) : Array Float :=
  LeanExe.build (t * t) fun e =>
    LeanExe.loop d 0.0 (fun c acc => acc + q[(e / t * d + c).toNat]! * k[(e % t * d + c).toNat]!) *
      scale + (if e % t ≤ e / t then 0.0 else -(1.0 / 0.0))

/-- The largest element of each of the `t` rows of width `w` of `x`. -/
def rowMax (x : Array Float) (t w : UInt64) : Array Float :=
  LeanExe.build t fun r => LeanExe.loop w (-(1.0 / 0.0)) fun c acc => max acc x[(r * w + c).toNat]!

/-- The sum of `exp (x[r][c] - mx[r])` over each of the `t` rows of width `w` of `x`. -/
def rowSumExp (x mx : Array Float) (t w : UInt64) : Array Float :=
  LeanExe.build t fun r =>
    LeanExe.loop w 0.0 fun c acc => acc + exp (x[(r * w + c).toNat]! - mx[r.toNat]!)

/-- `exp (x[r][c] - mx[r]) / sums[r]` for each element of the `t` rows of width `w`
of `x`. -/
def softmaxApply (x mx sums : Array Float) (t w : UInt64) : Array Float :=
  LeanExe.build (t * w) fun e => exp (x[e.toNat]! - mx[(e / w).toNat]!) / sums[(e / w).toNat]!

/-- The softmax of each of the `t` rows of width `w` of `x`. -/
def softmaxRows (x : Array Float) (t w : UInt64) : Array Float :=
  let mx := rowMax x t w
  let sums := rowSumExp x mx t w
  softmaxApply x mx sums t w

/-- Single-head causal self-attention on `t` rows of width `d`, with `d × d` weight
matrices stored by rows: `softmax (q kᵀ / √d, masked) · v · wo`, where `q`, `k`, and
`v` are `x · wq`, `x · wk`, and `x · wv`. -/
def attention (x wq wk wv wo : Array Float) (t d : UInt64) : Array Float :=
  let q := matMul x wq t d d
  let k := matMul x wk t d d
  let v := matMul x wv t d d
  let s := maskedScores q k t d (1.0 / d.toFloat.sqrt)
  let p := softmaxRows s t t
  let o := matMul p v t t d
  matMul o wo t d d

/-- A GPT-2 transformer block on `t` rows of width `d` with hidden width `f`:
`r = x + attention (layerNormRows x g1 b1)`, then `r + mlp (layerNormRows r g2 b2)`. -/
def block (x g1 b1 wq wk wv wo g2 b2 w1 w2 : Array Float) (t d f : UInt64) (eps : Float) :
    Array Float :=
  let h1 := layerNormRows x g1 b1 t d eps
  let a := attention h1 wq wk wv wo t d
  let r := add x a
  let h2 := layerNormRows r g2 b2 t d eps
  let m := mlp h2 w1 w2 t d f
  add r m

end LeanExe.Examples.Gpt
