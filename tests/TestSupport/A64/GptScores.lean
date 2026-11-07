import Demos.Gpt.Program
import LeanExe.Dialect.Build
import Verified.Reflect.Command

/-!
A GPT-2 kernel in binary64 as a bare-metal program for AArch64: `Demos.Gpt.scores`, which a host
calls after each `step` of generation, gives the scores of the cache's last position against every
token embedding.  It takes the hidden row of the cache's last block, applies the final layer norm,
`layerNormRows`, and multiplies by the embeddings with `matMulT`.  The configuration has one
layer, two heads of width 8, so a width of 16 and blocks of 48 values, a vocabulary of 32 tokens,
and GPT-2's `eps` of 1e-5.  The inputs come from the indices of their elements.  In the cache and
the embeddings, an element is an integer residue converted to binary64, divided by an odd
constant, which rounds most quotients, and shifted.  The gains and biases are dyadic values, which
binary64 holds exactly.  The entry is a wrapper, as CRC-32's and SHA-256's are in
`TestSupport.Bare`: `scoresCheck p` builds a cache of `p` positions, the embeddings, the gains,
and the biases, calls `scores`, and returns the words of the scores, since the bare-metal program
writes an array of words.  The Image passes 3.
-/

namespace TestSupport.A64.Gpt

open Demos.Gpt

/-- A cache of `p` positions of blocks of 48 values: element `e` is `(37 e mod 97) / 13 - 3.5`. -/
def cacheOf (p : UInt64) : Array Float :=
  LeanExe.build (p * 48) fun e => (e * 37 % 97).toFloat / 13.0 - 3.5

/-- The embeddings of `vocab` tokens of width `d`, stored by rows: element `e` is
`(53 e mod 89) / 41 - 1`. -/
def embeddings (vocab d : UInt64) : Array Float :=
  LeanExe.build (vocab * d) fun e => (e * 53 % 89).toFloat / 41.0 - 1.0

/-- The final layer norm's `d` gains: gain `c` is `1 + c / 32`. -/
def gains (d : UInt64) : Array Float :=
  LeanExe.build d fun c => 1.0 + c.toFloat / 32.0

/-- The final layer norm's `d` biases: bias `c` is `c / 64 - 0.125`. -/
def biases (d : UInt64) : Array Float :=
  LeanExe.build d fun c => c.toFloat / 64.0 - 0.125

/-- The words of the elements of `xs`. -/
def bits (xs : Array Float) : Array UInt64 :=
  LeanExe.build xs.size.toUInt64 fun i => xs[i.toNat]!.toBits

/-- The words of `scores` on the cache of `p` positions, with one layer, two heads of width 8, a
vocabulary of 32 tokens, and `eps` 1e-5. -/
def scoresCheck (p : UInt64) : Array UInt64 :=
  let cache := cacheOf p
  let wte := embeddings 32 16
  let gf := gains 16
  let bf := biases 16
  let s := scores cache wte gf bf 1 2 8 32 1e-5
  bits s

verified_compile compiled := [lastHidden, rowMeans, rowInvStd, normalizeRows, layerNormRows,
  Library.Numerics.LinearAlgebra.Float64.matMulT, scores, cacheOf, embeddings, gains, biases, bits,
  scoresCheck]

end TestSupport.A64.Gpt
