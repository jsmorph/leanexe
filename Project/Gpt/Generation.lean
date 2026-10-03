import Project.Gpt.Composites
import Project.Gpt.Exact

/-! The generation as the host runs it, in Talos terms.  The host calls `step` once per
token, each time handing over the cache that the previous call returned, which `step`
consumes, and calls `scores` on the last cache.  `Generating` describes a store between
these calls.  `generating_start` gives it for the empty cache, `generating_step` shows that
`step` gives it for one more token, and `generating_scores` shows that `scores` then returns
row `p` of `forward`.  Each call may abort at `unreachable`, as `Implements` allows, and
nothing bounds the memory the generation uses. -/

namespace Project.Gpt

open Wasm Project.Pipeline Project.IR Project.Runtime Project.Gpt.Exact

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
  cacheAfter tokens W.wte W.wpe W.g1 W.b1 W.wq W.bq W.wk W.bk W.wv W.bv W.wo W.bo W.g2 W.b2 W.wfc W.bfc W.wproj
    W.bproj layers nh dh f eps p

/-- A store between the calls of a generation: the allocator invariant holds, the memory's
cap is within the bound of `Implements`, every weight array is borrowed at its pointer and
lies apart from the object at `pc`, and the object at `pc` is owned and holds the cache of
the first `p` tokens. -/
def Generating (store : Store Unit) (W : Weights) (P : Pointers) (tokens : Array UInt64)
    (layers nh dh f : UInt64) (eps : Float) (pc : UInt64) (p : Nat) : Prop :=
  ∃ heap : Heap, heap.At store ∧ store.memoryCap gpt.module 0 ≤ 65535 ∧
    (∀ w ∈ W.pairs P, heap.Borrowed store w.1 (w.2.map Float.toBits) ∧
      regionsDisjoint (w.1.toNat, 8 * (w.2.size + 1)) (pc.toNat - 48, 48 + capacityAt store pc)) ∧
    heap.Owned store pc ((W.cache tokens layers nh dh f eps p).map Float.toBits)

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

/-- The host's starting store: the weights borrowed, and an owned empty array at `pc` apart
from them. -/
theorem generating_start {store : Store Unit} {heap : Heap} {W : Weights} {P : Pointers}
    {tokens : Array UInt64} {layers nh dh f : UInt64} {eps : Float} {pc : UInt64}
    (hAt : heap.At store) (hCap : store.memoryCap gpt.module 0 ≤ 65535)
    (hW : ∀ w ∈ W.pairs P, heap.Borrowed store w.1 (w.2.map Float.toBits) ∧
      regionsDisjoint (w.1.toNat, 8 * (w.2.size + 1)) (pc.toNat - 48, 48 + capacityAt store pc))
    (hC : heap.Owned store pc #[]) :
    Generating store W P tokens layers nh dh f eps pc 0 :=
  ⟨heap, hAt, hCap, hW, by simpa [Weights.cache, cacheAfter] using hC⟩

/-- The regions of the arrays that `step` reads: the weights of the blocks and the
embeddings, the first eighteen weight arrays. -/
theorem step_reads (pc : UInt64) (P : Pointers) (W : Weights) (cache : Array Float)
    (token layers nh dh f : UInt64) (eps : Float) :
    Represent.reads (stepArgs pc P token layers nh dh f eps)
      ((⟨cache⟩ : Moved (Array Float)), W.wte, W.wpe, W.g1, W.b1, W.wq, W.bq, W.wk, W.bk, W.wv,
        W.bv, W.wo, W.bo, W.g2, W.b2, W.wfc, W.bfc, W.wproj, W.bproj, token, layers, nh, dh, f,
        eps) =
      ((W.pairs P).take 18).map fun w => (w.1.toNat, 8 * ((w.2.map Float.toBits).size + 1)) :=
  rfl

/-- `step` on token `p` consumes the cache at `pc` and aborts or returns the cache of the
first `p + 1` tokens, leaving a store of the generation after `p + 1` tokens. -/
theorem generating_step {store : Store Unit} {W : Weights} {P : Pointers}
    {tokens : Array UInt64} {layers nh dh f : UInt64} {eps : Float} {pc : UInt64} {p : Nat}
    (env : HostEnv Unit) (h : Generating store W P tokens layers nh dh f eps pc p) :
    ReturnsOrAborts env gpt.module 41 store (stepArgs pc P tokens[p]! layers nh dh f eps).reverse
      fun final values => ∃ pc', values = [.i64 pc'] ∧
        Generating final W P tokens layers nh dh f eps pc' (p + 1) := by
  obtain ⟨heap, hAt, hCap, hW, hC⟩ := h
  have b : ∀ q a, (q, a) ∈ W.pairs P → heap.Borrowed store q (a.map Float.toBits) :=
    fun q a h => (hW _ h).1
  have hApart : ∀ w ∈ W.pairs P,
      Apart store [pc] (w.1.toNat, 8 * ((w.2.map Float.toBits).size + 1)) := fun w hw q hq => by
    rw [List.mem_singleton] at hq
    subst hq
    rw [Array.size_map]
    exact (hW w hw).2
  have hReads : ∀ r ∈ Represent.reads (stepArgs pc P tokens[p]! layers nh dh f eps)
      ((⟨W.cache tokens layers nh dh f eps p⟩ : Moved (Array Float)), W.wte, W.wpe, W.g1, W.b1,
        W.wq, W.bq, W.wk, W.bk, W.wv, W.bv, W.wo, W.bo, W.g2, W.b2, W.wfc, W.bfc, W.wproj,
        W.bproj, tokens[p]!, layers, nh, dh, f, eps), Apart store [pc] r := by
    rw [step_reads]
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact hApart w (List.mem_of_mem_take hw)
  refine (step_implements env store heap (stepArgs pc P tokens[p]! layers nh dh f eps)
    (⟨W.cache tokens layers nh dh f eps p⟩, W.wte, W.wpe, W.g1, W.b1, W.wq, W.bq, W.wk, W.bk,
      W.wv, W.bv, W.wo, W.bo, W.g2, W.b2, W.wfc, W.bfc, W.wproj, W.bproj, tokens[p]!, layers, nh,
      dh, f, eps) hAt
    ⟨[.i64 pc], _, rfl, ⟨pc, rfl, hC⟩, [.i64 P.wte], _, rfl, ⟨P.wte, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64
      P.wpe], _, rfl, ⟨P.wpe, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.g1], _, rfl, ⟨P.g1, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.b1], _,
      rfl, ⟨P.b1, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wq], _, rfl, ⟨P.wq, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bq], _, rfl, ⟨P.bq,
      rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wk], _, rfl, ⟨P.wk, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bk], _, rfl, ⟨P.bk, rfl, b _ _ (by simp [Weights.pairs])⟩,
      [.i64 P.wv], _, rfl, ⟨P.wv, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bv], _, rfl, ⟨P.bv, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wo],
      _, rfl, ⟨P.wo, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bo], _, rfl, ⟨P.bo, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.g2], _, rfl,
      ⟨P.g2, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.b2], _, rfl, ⟨P.b2, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wfc], _, rfl, ⟨P.wfc,
      rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bfc], _, rfl, ⟨P.bfc, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wproj], _, rfl, ⟨P.wproj, rfl,
      b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bproj], _, rfl, ⟨P.bproj, rfl, b _ _ (by simp [Weights.pairs])⟩, rfl⟩
    ⟨List.pairwise_singleton _ _, hReads⟩ hCap).mono ?_
  rintro final values ⟨heap', hAt', ⟨pc', hValues, hNew⟩, hCaps, hRegion⟩
  have hValues' : values = [.i64 pc'] := by
    rw [← List.reverse_reverse values, hValues]; rfl
  refine ⟨pc', hValues', heap', hAt', memoryCap_le_of_caps hCaps hCap, fun w hw => ⟨?_, ?_⟩, hNew⟩
  · obtain ⟨hBytes, hReg, -⟩ := hRegion _ (hW w hw).1.region (by simp) (hApart w hw)
    exact (hW w hw).1.keepIn hAt' hBytes hReg
  · have hDisjoint := (hRegion _ (hW w hw).1.region (by simp) (hApart w hw)).2.2
    rw [hValues] at hDisjoint
    have h := Represent.outside_float.mp hDisjoint
    rw [Array.size_map] at h
    exact h

/-- `scores` on the cache of the first `p + 1` tokens aborts or returns a new array that holds
row `p` of `forward` on any `T > p` tokens, under the bounds of `steps_exact`. -/
theorem generating_scores {store : Store Unit} {W : Weights} {P : Pointers}
    {tokens : Array UInt64} {layers T nh dh f vocab : UInt64} {eps : Float} {pc : UInt64}
    {p : Nat} (env : HostEnv Unit) (h : Generating store W P tokens layers nh dh f eps pc (p + 1))
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hn0 : 0 < nh.toNat) (hdh0 : 0 < dh.toNat) (hf : f.toNat < 2 ^ 32)
    (hv : vocab.toNat < 2 ^ 32) (hL : layers.toNat < 2 ^ 16)
    (hall : T.toNat * ((2 * layers.toNat + 1) * (nh.toNat * dh.toNat)) < 2 ^ 32) :
    ReturnsOrAborts env gpt.module 42 store (scoresArgs pc P layers nh dh vocab eps).reverse
      fun final values => ∃ r, values = [.i64 r] ∧ ∃ heap' : Heap, heap'.At final ∧
        heap'.Owned final r (((LeanExe.Examples.Gpt.forward tokens W.wte W.wpe W.g1 W.b1 W.wq W.bq W.wk W.bk W.wv W.bv W.wo W.bo W.g2 W.b2 W.wfc W.bfc W.wproj
          W.bproj W.gf W.bf layers T nh dh f vocab
          eps).extract (p * vocab.toNat) ((p + 1) * vocab.toNat)).map Float.toBits) := by
  obtain ⟨heap, hAt, hCap, hW, hC⟩ := h
  have b : ∀ q a, (q, a) ∈ W.pairs P → heap.Borrowed store q (a.map Float.toBits) :=
    fun q a h => (hW _ h).1
  refine (scores_implements env store heap (scoresArgs pc P layers nh dh vocab eps)
    (W.cache tokens layers nh dh f eps (p + 1), W.wte, W.gf, W.bf, layers, nh, dh, vocab, eps) hAt
    ⟨[.i64 pc], _, rfl, ⟨pc, rfl, hC.borrowed⟩, [.i64 P.wte], _, rfl, ⟨P.wte, rfl, b _ _ (by simp [Weights.pairs])⟩,
      [.i64 P.gf], _, rfl, ⟨P.gf, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bf], _, rfl, ⟨P.bf, rfl, b _ _ (by simp [Weights.pairs])⟩, rfl⟩
    Separate.nil hCap).mono ?_
  rintro final values ⟨heap', hAt', ⟨r, hValues, hOwned⟩, -⟩
  refine ⟨r, by rw [← List.reverse_reverse values, hValues]; rfl, heap', hAt', ?_⟩
  have hExact := steps_exact (tokens := tokens) (wte := W.wte) (wpe := W.wpe) (g1 := W.g1)
    (b1 := W.b1) (wq := W.wq) (bq := W.bq) (wk := W.wk) (bk := W.bk) (wv := W.wv) (bv := W.bv)
    (wo := W.wo) (bo := W.bo) (g2 := W.g2) (b2 := W.b2) (wfc := W.wfc) (bfc := W.bfc)
    (wproj := W.wproj) (bproj := W.bproj) (gf := W.gf) (bf := W.bf) (eps := eps)
    hp hT hn hdh hn0 hdh0 hf hv hL hall
  rw [← hExact]
  exact hOwned

end Project.Gpt
