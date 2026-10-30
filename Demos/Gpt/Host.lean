import Demos.Gpt.Exact
import LeanExe.Pipeline.Implements

/-! The weights of GPT-2 and the pointers at which the host holds them, the cache after the first
`p` tokens, and the arguments of the host's calls of `step` and `scores`.  The generation theorems
of the LeanExe module and of the verified module state the host's calls with these definitions.
`step_reads` gives the regions of the arrays that `step` reads. -/

namespace Demos.Gpt

open Wasm LeanExe.Pipeline LeanExe.Runtime Demos.Gpt.Exact

/-- The weight arrays of GPT-2, in the order the host passes them. -/
structure Weights where
  wte : Array Float
  wpe : Array Float
  g1 : Array Float
  b1 : Array Float
  wq : Array Float
  bq : Array Float
  wk : Array Float
  bk : Array Float
  wv : Array Float
  bv : Array Float
  wo : Array Float
  bo : Array Float
  g2 : Array Float
  b2 : Array Float
  wfc : Array Float
  bfc : Array Float
  wproj : Array Float
  bproj : Array Float
  gf : Array Float
  bf : Array Float

/-- The pointers at which the host holds the weight arrays. -/
structure Pointers where
  wte : UInt64
  wpe : UInt64
  g1 : UInt64
  b1 : UInt64
  wq : UInt64
  bq : UInt64
  wk : UInt64
  bk : UInt64
  wv : UInt64
  bv : UInt64
  wo : UInt64
  bo : UInt64
  g2 : UInt64
  b2 : UInt64
  wfc : UInt64
  bfc : UInt64
  wproj : UInt64
  bproj : UInt64
  gf : UInt64
  bf : UInt64

/-- Each weight array with its pointer. -/
def Weights.pairs (W : Weights) (P : Pointers) : List (UInt64 × Array Float) :=
  [(P.wte, W.wte), (P.wpe, W.wpe), (P.g1, W.g1), (P.b1, W.b1), (P.wq, W.wq), (P.bq, W.bq),
   (P.wk, W.wk), (P.bk, W.bk), (P.wv, W.wv), (P.bv, W.bv), (P.wo, W.wo), (P.bo, W.bo), (P.g2,
   W.g2), (P.b2, W.b2), (P.wfc, W.wfc), (P.bfc, W.bfc), (P.wproj, W.wproj), (P.bproj, W.bproj),
   (P.gf, W.gf), (P.bf, W.bf)]

/-- The cache after the first `p` tokens. -/
abbrev Weights.cache (W : Weights) (tokens : Array UInt64) (layers nh dh f : UInt64) (eps : Float)
    (p : Nat) : Array Float :=
  cacheAfter tokens W.wte W.wpe W.g1 W.b1 W.wq W.bq W.wk W.bk W.wv W.bv W.wo W.bo W.g2 W.b2 W.wfc
    W.bfc W.wproj W.bproj layers nh dh f eps p

/-- The arguments of `step` for the cache at `pc` and the token `token`. -/
def stepArgs (pc : UInt64) (P : Pointers) (token layers nh dh f : UInt64) (eps : Float) :
    List Value :=
  [.i64 pc, .i64 P.wte, .i64 P.wpe, .i64 P.g1, .i64 P.b1, .i64 P.wq, .i64 P.bq, .i64 P.wk, .i64
   P.bk, .i64 P.wv, .i64 P.bv, .i64 P.wo, .i64 P.bo, .i64 P.g2, .i64 P.b2, .i64 P.wfc, .i64
   P.bfc, .i64 P.wproj, .i64 P.bproj, .i64 token, .i64 layers, .i64 nh, .i64 dh, .i64 f, .f64
   eps.toBits]

/-- The arguments of `scores` for the cache at `pc`. -/
def scoresArgs (pc : UInt64) (P : Pointers) (layers nh dh vocab : UInt64) (eps : Float) :
    List Value :=
  [.i64 pc, .i64 P.wte, .i64 P.gf, .i64 P.bf, .i64 layers, .i64 nh, .i64 dh, .i64 vocab,
    .f64 eps.toBits]

/-- The regions of the arrays that `step` reads: the weights of the blocks and the
embeddings, the first eighteen weight arrays. -/
theorem step_reads (store : Store Unit) (pc : UInt64) (P : Pointers) (W : Weights)
    (cache : Array Float) (token layers nh dh f : UInt64) (eps : Float) :
    Represent.reads store (stepArgs pc P token layers nh dh f eps)
      ((⟨cache⟩ : Moved (Array Float)), W.wte, W.wpe, W.g1, W.b1, W.wq, W.bq, W.wk, W.bk, W.wv,
        W.bv, W.wo, W.bo, W.g2, W.b2, W.wfc, W.bfc, W.wproj, W.bproj, token, layers, nh, dh, f,
        eps) =
      ((W.pairs P).take 18).map fun w => (w.1.toNat, 8 * ((w.2.map Float.toBits).size + 1)) :=
  rfl

end Demos.Gpt
