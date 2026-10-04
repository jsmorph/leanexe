import LeanExe.Build
import LeanExe.Loop
import LeanExe.Float32

/-!
GPT-2 124M in binary32, written for WGSL kernels: every array is built element by element, and
the functions that kernels share are marked `@[inline]`, so that the compiler unfolds them into
each kernel.
-/

namespace LeanExe.Examples.Gpt32

/-- `e^x` in binary32.  The argument is clamped to `[-104, 89]`, which maps a NaN to 89;
`k = nearest (c · log₂ e)` and `r = c - k · ln 2` with `ln 2` in two parts, the first with nine
significant bits so that `k · 0.693359375` is exact.  The Taylor polynomial of degree 7 gives
`e^r`, which is multiplied by `2^k` as two normal powers of two built from their bits, with
`k + 254` taken from the bits of `k + 1.5 · 2^23`.  Against correctly rounded results the error
is at most 1.19 ulp over `[-90, 90]` (review of 2026-10-04); no theorem bounds it. -/
@[inline] def exp32 (x : Float32) : Float32 :=
  let a := if x ≤ 89.0 then x else 89.0
  let c := if -104.0 ≤ a then a else -104.0
  let kf := LeanExe.Float32.nearest (c * 1.44269502162933349609375)
  let r := c - kf * 0.693359375 + kf * 0.000212194441701285541057586669921875
  let p := 1.0 + r * (1.0 + r * (0.5 + r * (0.16666667163372039794921875 +
    r * (0.0416666679084300994873046875 + r * (0.008333333767950534820556640625 +
    r * (0.001388888922519981861114501953125 + r * 0.000198412701138295233249664306640625))))))
  let m := (kf + 12582912.0).toBits.toUInt64 - 1262485250
  let h := m / 2
  p * Float32.ofBits (h * 8388608).toUInt32 * Float32.ofBits ((m - h) * 8388608).toUInt32

/-- `exp32` of each element of `x`. -/
def expArray32 (x : Array Float32) : Array Float32 :=
  LeanExe.build x.size.toUInt64 fun i => exp32 x[i.toNat]!

/-- GPT-2's GELU, `0.5 x (1 + tanh z)` with `z = √(2/π) (x + 0.044715 x³)` and `√(2/π)` rounded
to binary32.  With `tanh z = 1 - 2 / (e^(2z) + 1)`, `1 + tanh z` is `2 - 2 / (e^(2z) + 1)`; the
function takes that form because SwiftShader folds `1 + (1 - q)` into `2 - q`, which WGSL
allows. -/
@[inline] def gelu32 (x : Float32) : Float32 :=
  0.5 * x * (2.0 - 2.0 / (exp32 (2.0 * (0.79788458347320556640625 * (x + 0.044715 * x * x * x))) + 1.0))

/-! The kernels of one token's step.  A row has `d` elements; the attention of position `p` reads
the keys and values of positions `0` to `p` from one layer's cache, a row per position.  Scores
lie by head with a stride of 1,024 positions, GPT-2's context length, so that the head and the
position of an element come from a division by a power of two; a head has 64 elements. -/

/-- The embedding of the token at row `row` of `wte`, a chunk of the token embeddings, at
position `p`. -/
def embed32 (wte wpe : Array Float32) (row p d : UInt64) : Array Float32 :=
  LeanExe.build d fun c => wte[(row * d + c).toNat]! + wpe[(p * d + c).toNat]!

/-- The layer normalization of the row `x` of `d` elements, with gain `g`, bias `b`, and
`nf = d` as a float; each element computes the mean and the variance itself. -/
def layerNorm32 (x g b : Array Float32) (d : UInt64) (nf : Float32) : Array Float32 :=
  LeanExe.build d fun c =>
    let mean := LeanExe.loop d 0.0 (fun i acc => acc + x[i.toNat]!) / nf
    let var := LeanExe.loop d 0.0 (fun i acc => acc + (x[i.toNat]! - mean) * (x[i.toNat]! - mean)) / nf
    (x[c.toNat]! - mean) * (1.0 / (var + 0.00001).sqrt) * g[c.toNat]! + b[c.toNat]!

/-- The row `x` of `k` elements times the `k × m` matrix `w`, stored by rows, plus the bias
`b`. -/
def linear32 (x w b : Array Float32) (k m : UInt64) : Array Float32 :=
  LeanExe.build m fun c =>
    LeanExe.loop k 0.0 (fun i acc => acc + x[i.toNat]! * w[(i * m + c).toNat]!) + b[c.toNat]!

/-- `cache` of `base` elements followed by `row`, `n` elements in all. -/
def append32 (cache row : Array Float32) (base n : UInt64) : Array Float32 :=
  LeanExe.build n fun e => if e < base then cache[e.toNat]! else row[(e - base).toNat]!

/-- The scores of position `p`: element `h · 1024 + j` is the scaled dot product of head `h` of
the query `q` and of the key of position `j ≤ p` in `kc`, rows of `d` elements, and 0 for
`j > p`.  Every element computes its dot product, since the compiler takes no loop in a
branch. -/
def scores32 (q kc : Array Float32) (p d n : UInt64) : Array Float32 :=
  LeanExe.build n fun e =>
    let dot := LeanExe.loop 64 0.0 (fun t acc =>
      acc + q[(e / 1024 * 64 + t).toNat]! * kc[(e % 1024 * d + e / 1024 * 64 + t).toNat]!)
    if e % 1024 ≤ p then dot * 0.125 else 0.0

/-- The largest score of each of the `nh` heads over positions `0` to `p`. -/
def headMax32 (s : Array Float32) (p nh : UInt64) : Array Float32 :=
  LeanExe.build nh fun h =>
    LeanExe.loop p s[(h * 1024).toNat]! (fun j acc => max acc s[(h * 1024 + j + 1).toNat]!)

/-- The sum of `exp32 (s - max)` of each of the `nh` heads over positions `0` to `p`. -/
def headSum32 (s mx : Array Float32) (p nh : UInt64) : Array Float32 :=
  LeanExe.build nh fun h =>
    LeanExe.loop (p + 1) 0.0 (fun j acc => acc + exp32 (s[(h * 1024 + j).toNat]! - mx[h.toNat]!))

/-- The attention weights: `exp32 (s - max) / sum` for positions `0` to `p` of each head, and 0
beyond. -/
def probs32 (s mx sm : Array Float32) (p n : UInt64) : Array Float32 :=
  LeanExe.build n fun e =>
    let w := exp32 (s[e.toNat]! - mx[(e / 1024).toNat]!) / sm[(e / 1024).toNat]!
    if e % 1024 ≤ p then w else 0.0

/-- The attention output: element `c` sums the weights of its head `c / 64` times element `c`
of the values of positions `0` to `p` in `vc`, rows of `d` elements. -/
def mix32 (pw vc : Array Float32) (p d : UInt64) : Array Float32 :=
  LeanExe.build d fun c =>
    LeanExe.loop (p + 1) 0.0 (fun j acc => acc + pw[(c / 64 * 1024 + j).toNat]! * vc[(j * d + c).toNat]!)

/-- The element-wise sum of `a` and `b`. -/
def add32 (a b : Array Float32) : Array Float32 :=
  LeanExe.build a.size.toUInt64 fun i => a[i.toNat]! + b[i.toNat]!

/-- `gelu32` of each element of `x`. -/
def geluArray32 (x : Array Float32) : Array Float32 :=
  LeanExe.build x.size.toUInt64 fun i => gelu32 x[i.toNat]!

/-- The scores of the hidden row `h` of `d` elements against the `rows` rows of `wte`, a chunk
of the token embeddings. -/
def logits32 (h wte : Array Float32) (rows d : UInt64) : Array Float32 :=
  LeanExe.build rows fun v => LeanExe.loop d 0.0 (fun c acc => acc + h[c.toNat]! * wte[(v * d + c).toNat]!)

end LeanExe.Examples.Gpt32
