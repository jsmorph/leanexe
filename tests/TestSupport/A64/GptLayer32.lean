import Demos.Gpt32.Program
import LeanExe.Dialect.Build
import Verified.Reflect.Command

/-!
A layer of GPT-2 in binary32 as a bare-metal program for AArch64: the step of one transformer
layer, `Demos.Gpt32.layerStep32`, for a model of one head, so a width of 64, and an MLP of width 64,
at position `p` with the caches of the positions before it.  The step applies the first layer
norm, the query, key, and value projections, the attention, whose scores, maxima, sums, and weights
use `exp32` and so `FRINTN`, the output projection with the residual, the second layer norm, the
MLP with GELU, and the second residual.  The entry is a wrapper, as the binary64 kernel's is in
`TestSupport.A64.GptScores`: `layerCheck p` builds the row, the caches of `p` positions, and the
layer's weights from the indices of their elements with `vals`, applies the kernels in the order
of `layerStep32`'s body, and returns the words of the row after the layer.  The Image passes 2.
-/

namespace TestSupport.A64.Gpt32

open Demos.Gpt32 Library.Numerics.LinearAlgebra.Binary32

/-- `n` binary32 values: element `e` is `((a e + b) mod q) / c - o`. -/
def vals (n a b q : UInt64) (c o : Float32) : Array Float32 :=
  LeanExe.build n fun e => ((e * a + b) % q).toFloat32 / c - o

/-- The words of the elements of `xs`, zero-extended. -/
def bits32 (xs : Array Float32) : Array UInt64 :=
  LeanExe.build xs.size.toUInt64 fun i => xs[i.toNat]!.toBits.toUInt64

/-- The words of the row after one layer at position `p` of a model of one head and an MLP of
width 64, with the row, the caches, and the weights that `vals` gives. -/
def layerCheck (p : UInt64) : Array UInt64 :=
  let x := vals 64 37 5 97 13.0 3.5
  let kc := vals (p * 64) 53 7 89 41.0 1.0
  let vc := vals (p * 64) 29 3 83 37.0 1.0
  let g1 := vals 64 7 32 64 32.0 0.0
  let b1 := vals 64 5 1 64 64.0 0.5
  let wq := vals 4096 31 2 101 409.0 0.125
  let bq := vals 64 3 1 17 64.0 0.125
  let wk := vals 4096 43 9 103 409.0 0.125
  let bk := vals 64 11 2 19 64.0 0.125
  let wv := vals 4096 47 4 107 409.0 0.125
  let bv := vals 64 13 3 23 64.0 0.125
  let wo := vals 4096 59 6 109 409.0 0.125
  let bo := vals 64 17 4 29 64.0 0.125
  let g2 := vals 64 9 32 64 32.0 0.0
  let b2 := vals 64 7 5 64 64.0 0.5
  let wfc := vals 4096 61 8 113 409.0 0.125
  let bfc := vals 64 19 5 31 64.0 0.125
  let wproj := vals 4096 67 10 127 409.0 0.125
  let bproj := vals 64 23 6 37 64.0 0.125
  let h1 := layerNorm32 x g1 b1 64 (64 : UInt64).toFloat32
  let q := linear32 h1 wq bq 64 64
  let k := linear32 h1 wk bk 64 64
  let v := linear32 h1 wv bv 64 64
  let kc' := append32 kc k (p * 64) ((p + 1) * 64)
  let vc' := append32 vc v (p * 64) ((p + 1) * 64)
  let sc := scores32 q kc' p 64 1024
  let mx := headMax32 sc p 1
  let sm := headSum32 sc mx p 1
  let pw := probs32 sc mx sm p 1024
  let o := mix32 pw vc' p 64
  let r := add32 x (linear32 o wo bo 64 64)
  let h2 := layerNorm32 r g2 b2 64 (64 : UInt64).toFloat32
  let g := geluArray32 (linear32 h2 wfc bfc 64 64)
  bits32 (add32 r (linear32 g wproj bproj 64 64))

verified_compile compiled := [layerNorm32, linear32, append32, scores32, headMax32, headSum32,
  probs32, mix32, add32, geluArray32, vals, bits32, layerCheck]

end TestSupport.A64.Gpt32
