import LeanExe.Loop
import LeanExe.Build
import LeanExe.Examples.Prng

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

/-- The linear layer `x · w + b` for the `n × k` matrix `x` stored by rows, with layer
`l` of the weights: `w` holds one `k × m` matrix stored by rows for each layer, one after
another, and `b` one `m`-element bias for each layer, so layer `l` starts at `l · k · m`
in `w` and at `l · m` in `b`.  Each element sums the products first and then adds the
bias. -/
def linear (x w b : Array Float) (l n k m : UInt64) : Array Float :=
  LeanExe.build (n * m) fun e =>
    LeanExe.loop k 0.0 (fun c acc =>
        acc + x[(e / m * k + c).toNat]! * w[(l * (k * m) + (c * m + e % m)).toNat]!) +
      b[(l * m + e % m).toNat]!

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

/-- The MLP of a transformer block on `t` rows of width `d` with hidden width `f` and
layer `l` of the weights: `gelu (x · wfc + bfc) · wproj + bproj`, where `x` is `t × d`,
`wfc` is `d × f`, and `wproj` is `f × d`. -/
def mlp (x wfc bfc wproj bproj : Array Float) (l t d f : UInt64) : Array Float :=
  let h := linear x wfc bfc l t d f
  let g := geluArray h
  linear g wproj bproj l t f d

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
inverse deviations, then scaled by layer `l` of `g` and shifted by layer `l` of `b`,
which hold `d` values for each layer. -/
def normalizeRows (x means invStd g b : Array Float) (l t d : UInt64) : Array Float :=
  LeanExe.build (t * d) fun e =>
    (x[e.toNat]! - means[(e / d).toNat]!) * invStd[(e / d).toNat]! * g[(l * d + e % d).toNat]! +
      b[(l * d + e % d).toNat]!

/-- The layer normalization of each of the `t` rows of width `d` of `x`, with layer `l`
of the gains `g` and biases `b`. -/
def layerNormRows (x g b : Array Float) (l t d : UInt64) (eps : Float) : Array Float :=
  let means := rowMeans x t d
  let inv := rowInvStd x means t d eps
  normalizeRows x means inv g b l t d

/-- The causally masked attention scores of `nh` heads of width `dh`, for `t` queries
and keys stored by rows of width `nh · dh`, as `t` rows of `nh` blocks of `t` scores.
Element `(i, h, j)` is `scale · (q[i] · k[j])` over the columns of head `h` where
`j ≤ i`, and `0 · scale` elsewhere, which the softmax does not read.  A masked element
reads no key, so row `i` depends only on rows `0` to `i`. -/
def maskedScores (q k : Array Float) (t nh dh : UInt64) (scale : Float) : Array Float :=
  LeanExe.build (t * nh * t) fun e =>
    LeanExe.loop (if e % t ≤ e / (nh * t) then dh else 0) 0.0
      (fun c acc => acc + q[(e / (nh * t) * (nh * dh) + (e / t % nh * dh + c)).toNat]! *
        k[(e % t * (nh * dh) + (e / t % nh * dh + c)).toNat]!) * scale

/-- The largest of elements `0` to `r / nh` of each row `r` of the `t · nh` rows of width
`t` of attention scores `x`: row `r` holds the scores of position `r / nh`, which sees
positions `0` to `r / nh`. -/
def rowMax (x : Array Float) (t nh : UInt64) : Array Float :=
  LeanExe.build (t * nh) fun r =>
    LeanExe.loop (r / nh + 1) (-(1.0 / 0.0)) fun c acc => max acc x[(r * t + c).toNat]!

/-- The sum of `exp (x[r][c] - mx[r])` over elements `0` to `r / nh` of each row `r` of the
`t · nh` rows of width `t` of attention scores `x`. -/
def rowSumExp (x mx : Array Float) (t nh : UInt64) : Array Float :=
  LeanExe.build (t * nh) fun r =>
    LeanExe.loop (r / nh + 1) 0.0 fun c acc => acc + exp (x[(r * t + c).toNat]! - mx[r.toNat]!)

/-- `exp (x[r][c] - mx[r]) / sums[r]` for each element of the `t` rows of width `w`
of `x`. -/
def softmaxApply (x mx sums : Array Float) (t w : UInt64) : Array Float :=
  LeanExe.build (t * w) fun e => exp (x[e.toNat]! - mx[(e / w).toNat]!) / sums[(e / w).toNat]!

/-- The causal softmax of each of the `t · nh` rows of width `t` of attention scores `x`
over its elements `0` to `r / nh`.  The later elements of row `r` are computed from
scores that `causalMatMul` does not read. -/
def softmaxRows (x : Array Float) (t nh : UInt64) : Array Float :=
  let mx := rowMax x t nh
  let sums := rowSumExp x mx t nh
  softmaxApply x mx sums (t * nh) t

/-- The product of the attention weights `p`, `t` rows of `nh` blocks of `t`, and the
values `v`, `t` rows of width `nh · dh`: element `(i, c)` sums `p[i][h][j] · v[j][c]`
over `j ≤ i` only, where `h = c / dh` is the head of column `c`. -/
def causalMatMul (p v : Array Float) (t nh dh : UInt64) : Array Float :=
  LeanExe.build (t * (nh * dh)) fun e =>
    LeanExe.loop (e / (nh * dh) + 1) 0.0 fun j acc =>
      acc + p[(e / (nh * dh) * (nh * t) + (e % (nh * dh) / dh * t + j)).toNat]! *
        v[(j * (nh * dh) + e % (nh * dh)).toNat]!

/-- Causal self-attention with `nh` heads of width `dh` on `t` rows of width
`d = nh · dh`, with `d × d` weight matrices stored by rows: for each head,
`softmax (q kᵀ / √dh, masked) · v` over that head's columns, then `· wo + bo`, where
`q`, `k`, and `v` are `x · wq + bq`, `x · wk + bk`, and `x · wv + bv`.  Row `i` depends
only on rows `0` to `i` of `x`: `maskedScores` reads no later key, and `causalMatMul`
reads no later value. -/
def attention (x wq bq wk bk wv bv wo bo : Array Float) (l t nh dh : UInt64) : Array Float :=
  let q := linear x wq bq l t (nh * dh) (nh * dh)
  let k := linear x wk bk l t (nh * dh) (nh * dh)
  let v := linear x wv bv l t (nh * dh) (nh * dh)
  let s := maskedScores q k t nh dh (1.0 / dh.toFloat.sqrt)
  let p := softmaxRows s t nh
  let o := causalMatMul p v t nh dh
  linear o wo bo l t (nh * dh) (nh * dh)

/-- A GPT-2 transformer block in binary64 arithmetic on `t` rows of width `nh · dh`,
with `nh` heads, hidden width `f`, and layer `l` of the weights:
`r = x + attention (layerNormRows x g1 b1)`, then `r + mlp (layerNormRows r g2 b2)`.  The
weights follow GPT-2's order, with the `q`, `k`, and `v` parts of `c_attn` as separate
matrices, and each array holds the weights of every layer one after another: `g1` holds
`d` values per layer, `wq` holds `d × d`, `wfc` holds `d × f`, and so on, where
`d = nh · dh`. -/
def block (x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float)
    (l t nh dh f : UInt64) (eps : Float) : Array Float :=
  let h1 := layerNormRows x g1 b1 l t (nh * dh) eps
  let a := attention h1 wq bq wk bk wv bv wo bo l t nh dh
  let r := add x a
  let h2 := layerNormRows r g2 b2 l t (nh * dh) eps
  let m := mlp h2 wfc bfc wproj bproj l t (nh * dh) f
  add r m

/-- The embeddings of `t` tokens as `t` rows of width `d`: row `i` is row
`tokens[i]` of `wte` plus row `i` of `wpe`, with 0 for each missing element. -/
def embed (tokens : Array UInt64) (wte wpe : Array Float) (t d : UInt64) : Array Float :=
  LeanExe.build (t * d) fun e =>
    wte[(tokens[(e / d).toNat]! * d + e % d).toNat]! + wpe[e.toNat]!

/-- The product of the `n × k` matrix `a` and the transpose of the `m × k` matrix
`b`, both stored by rows, as an `n × m` matrix stored by rows. -/
def matMulT (a b : Array Float) (n k m : UInt64) : Array Float :=
  LeanExe.build (n * m) fun e =>
    LeanExe.loop k 0.0 fun c acc => acc + a[(e / m * k + c).toNat]! * b[(e % m * k + c).toNat]!

/-- The forward pass of a GPT-2 model with `layers` blocks in binary64 arithmetic on
`t` tokens, with `nh` heads of width `dh`, hidden width `f`, and `vocab` token
embeddings: the embeddings, the blocks, whose weights are stacked layer after layer
as `block` takes them, a final layer norm, and the scores of each position against
every token embedding, as `t` rows of width `vocab`. -/
def forward (tokens : Array UInt64) (wte wpe : Array Float)
    (g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float)
    (gf bf : Array Float) (layers t nh dh f vocab : UInt64) (eps : Float) : Array Float :=
  let x0 := embed tokens wte wpe t (nh * dh)
  let x := LeanExe.loop layers x0 fun l x =>
    block x g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj l t nh dh f eps
  let h := layerNormRows x gf bf 0 t (nh * dh) eps
  matMulT h wte t (nh * dh) vocab

/-! The cached step.  A cache holds one block of `bsize = (2 · layers + 1) · d` values per
position: the position's final hidden row, then its key and value for each layer.  `step`
computes the next position's block from the cache and appends it, and `scores` computes
the scores of the last position from its hidden row.  Each kernel performs the operations
of the corresponding row of `forward`, in the same order. -/

/-- The block that `step` starts from for `token` at position `p`: its embedding, row
`token` of `wte` plus row `p` of `wpe`, followed by zeros up to `bsize`. -/
def embedBlock (wte wpe : Array Float) (token p d bsize : UInt64) : Array Float :=
  LeanExe.build bsize fun e =>
    if e < d then wte[(token * d + e).toNat]! + wpe[(p * d + e).toNat]! else 0.0

/-- The first `d` elements of `s`: the hidden row in a block. -/
def firstRow (s : Array Float) (d : UInt64) : Array Float :=
  LeanExe.build d fun c => s[c.toNat]!

/-- The scores of position `p` with `nh` heads of width `dh`, as `nh` rows of `p + 1`:
score `j` of head `h` is `scale · (q · k_j)` over the head's columns, where `k_j` is the
key of layer `l` in block `j` of `cache` for `j < p`, and `k` for `j = p`. -/
def stepScores (q k cache : Array Float) (l p nh dh bsize : UInt64) (scale : Float) :
    Array Float :=
  LeanExe.build (nh * (p + 1)) fun e =>
    LeanExe.loop dh 0.0 (fun c acc => acc + q[(e / (p + 1) * dh + c).toNat]! *
      (if e % (p + 1) < p then
        cache[(e % (p + 1) * bsize + (2 * l + 1) * (nh * dh) + (e / (p + 1) * dh + c)).toNat]!
      else k[(e / (p + 1) * dh + c).toNat]!)) * scale

/-- The largest of the `w` elements of each of the `nh` rows of `s`. -/
def headMax (s : Array Float) (nh w : UInt64) : Array Float :=
  LeanExe.build nh fun h => LeanExe.loop w (-(1.0 / 0.0)) fun c acc => max acc s[(h * w + c).toNat]!

/-- The sum of `exp (s[h][c] - mx[h])` over each of the `nh` rows of width `w` of `s`. -/
def headSumExp (s mx : Array Float) (nh w : UInt64) : Array Float :=
  LeanExe.build nh fun h =>
    LeanExe.loop w 0.0 fun c acc => acc + exp (s[(h * w + c).toNat]! - mx[h.toNat]!)

/-- The softmax of each of the `nh` rows of width `w` of `s`. -/
def stepSoftmax (s : Array Float) (nh w : UInt64) : Array Float :=
  let mx := headMax s nh w
  let sums := headSumExp s mx nh w
  softmaxApply s mx sums nh w

/-- The attention output of position `p`: element `c` sums `pw[h][j] · v_j[c]` over
`j ≤ p`, where `h = c / dh` and `v_j` is the value of layer `l` in block `j` of `cache` for
`j < p`, and `v` for `j = p`. -/
def stepMix (pw v cache : Array Float) (l p nh dh bsize : UInt64) : Array Float :=
  LeanExe.build (nh * dh) fun c =>
    LeanExe.loop (p + 1) 0.0 fun j acc => acc + pw[(c / dh * (p + 1) + j).toNat]! *
      (if j < p then cache[(j * bsize + (2 * l + 2) * (nh * dh) + c).toNat]! else v[c.toNat]!)

/-- `s` with its hidden row replaced by `x` and the key and value of layer `l` by `k` and
`v`, in blocks of rows of width `d`. -/
def writeBlock (s x k v : Array Float) (l d : UInt64) : Array Float :=
  LeanExe.build s.size.toUInt64 fun e =>
    if e < d then x[e.toNat]!
    else if e < (2 * l + 1) * d then s[e.toNat]!
    else if e < (2 * l + 2) * d then k[(e - (2 * l + 1) * d).toNat]!
    else if e < (2 * l + 3) * d then v[(e - (2 * l + 2) * d).toNat]!
    else s[e.toNat]!

/-- `cache` followed by `s`. -/
def appendBlock (cache s : Array Float) : Array Float :=
  let n := cache.size.toUInt64
  LeanExe.build (n + s.size.toUInt64) fun e => if e < n then cache[e.toNat]! else s[(e - n).toNat]!

/-- The hidden row of the last block of `cache`. -/
def lastHidden (cache : Array Float) (d bsize : UInt64) : Array Float :=
  let n := cache.size.toUInt64
  LeanExe.build d fun c => cache[(n - bsize + c).toNat]!

/-- Layer `l` of `step`: the row of block `s` through `block`'s computation for position
`p`, with attention over the keys and values of `cache` and of this position. -/
def layerStep (s cache g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float)
    (l p nh dh f bsize : UInt64) (eps : Float) : Array Float :=
  let x := firstRow s (nh * dh)
  let h1 := layerNormRows x g1 b1 l 1 (nh * dh) eps
  let q := linear h1 wq bq l 1 (nh * dh) (nh * dh)
  let k := linear h1 wk bk l 1 (nh * dh) (nh * dh)
  let v := linear h1 wv bv l 1 (nh * dh) (nh * dh)
  let sc := stepScores q k cache l p nh dh bsize (1.0 / dh.toFloat.sqrt)
  let pw := stepSoftmax sc nh (p + 1)
  let o := stepMix pw v cache l p nh dh bsize
  let a := linear o wo bo l 1 (nh * dh) (nh * dh)
  let r := add x a
  let h2 := layerNormRows r g2 b2 l 1 (nh * dh) eps
  let m := mlp h2 wfc bfc wproj bproj l 1 (nh * dh) f
  let y := add r m
  writeBlock s y k v l (nh * dh)

/-- The cache after `token`: `cache` followed by the block of the next position, whose
number is the number of blocks in `cache`. -/
def step (cache wte wpe g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj : Array Float)
    (token layers nh dh f : UInt64) (eps : Float) : Array Float :=
  let bsize := (2 * layers + 1) * (nh * dh)
  let p := cache.size.toUInt64 / (if bsize = 0 then 1 else bsize)
  let s0 := embedBlock wte wpe token p (nh * dh) bsize
  let s := LeanExe.loop layers s0 fun l s =>
    layerStep s cache g1 b1 wq bq wk bk wv bv wo bo g2 b2 wfc bfc wproj bproj l p nh dh f bsize eps
  appendBlock cache s

/-- The scores of the last position of `cache` against every token embedding. -/
def scores (cache wte gf bf : Array Float) (layers nh dh vocab : UInt64) (eps : Float) :
    Array Float :=
  let x := lastHidden cache (nh * dh) ((2 * layers + 1) * (nh * dh))
  let h := layerNormRows x gf bf 0 1 (nh * dh) eps
  matMulT h wte 1 (nh * dh) vocab

/-! Top-k sampling.  `sampleTopK` keeps every token whose score is at least the `k`-th
largest score, counted with repeats, as Hugging Face's `TopKLogitsWarper` does, and draws
one of them with weight `exp ((score - max) / temperature)`, using one SplitMix64 step. -/

/-- `k` copies of `-∞`: the empty buffer of the `k` largest scores. -/
def negInfs (k : UInt64) : Array Float :=
  LeanExe.build k fun _ => -(1.0 / 0.0)

/-- The buffer `buf` of the `k` largest scores, in descending order, with score `i` of `s`
inserted after the entries at or above it.  A score below every entry, or NaN, leaves the
buffer unchanged. -/
def insertTop (buf s : Array Float) (i k : UInt64) : Array Float :=
  let x := s[i.toNat]!
  let pos := LeanExe.loop k 0 fun j p => if buf[j.toNat]! < x then p else p + 1
  LeanExe.build k fun j =>
    if j < pos then buf[j.toNat]! else if j = pos then x else buf[(j - 1).toNat]!

/-- The `k` largest scores of `s` in descending order, counted with repeats and padded
with `-∞`. -/
def topKBuffer (s : Array Float) (k : UInt64) : Array Float :=
  let init := negInfs k
  LeanExe.loop s.size.toUInt64 init fun i b => insertTop b s i k

/-- Draws a token from the scores of `s` at or above `buf[k - 1]`, the threshold, with
weights `exp ((score - buf[0]) / temperature)`: one SplitMix64 step from `state` gives
`u` in `[0, 1)`, and the token is the first whose running weight exceeds `u` times the
total, or the last kept token if rounding leaves none.  Returns the token and the next
state. -/
def sampleFrom (s buf : Array Float) (k : UInt64) (temperature : Float) (state : UInt64) :
    UInt64 × UInt64 :=
  let threshold := buf[(k - 1).toNat]!
  let m := buf[(0 : UInt64).toNat]!
  let n := s.size.toUInt64
  let total := LeanExe.loop n 0.0 fun i acc =>
    if threshold ≤ s[i.toNat]! then acc + exp ((s[i.toNat]! - m) / temperature) else acc
  let (next, x) := LeanExe.Examples.Prng.splitMix state
  let target := LeanExe.Examples.Prng.unitFloat x * total
  let (_, pick, last) := LeanExe.loop n (0.0, n, n) fun i (acc, pick, last) =>
    let acc' := if threshold ≤ s[i.toNat]! then acc + exp ((s[i.toNat]! - m) / temperature)
      else acc
    (acc', if threshold ≤ s[i.toNat]! then (if pick = n then (if target < acc' then i else pick)
        else pick) else pick,
      if threshold ≤ s[i.toNat]! then i else last)
  (if pick = n then last else pick, next)

/-- Top-k sampling from the scores `s` with `k` at least 1, temperature `temperature`,
and generator state `state`: the chosen token and the next state. -/
def sampleTopK (s : Array Float) (k : UInt64) (temperature : Float) (state : UInt64) :
    UInt64 × UInt64 :=
  let k1 := if k = 0 then 1 else k
  let buf := topKBuffer s k1
  sampleFrom s buf k1 temperature state

end LeanExe.Examples.Gpt
