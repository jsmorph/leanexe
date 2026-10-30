import Demos.Gpt.Composites
import Demos.Gpt.Host

/-! The generation as the host runs it, in Talos terms.  The host calls `step` once per
token, each time handing over the cache that the previous call returned, which `step`
consumes, and calls `scores` on the last cache.  `Generating` describes a store between
these calls.  `generating_start` gives it for the empty cache, `generating_step` shows that
`step` gives it for one more token, and `generating_scores` shows that `scores` then returns
row `p` of `forward`.  Each call may abort at `unreachable`, as `Implements` allows, and
nothing bounds the memory the generation uses. -/

namespace Demos.Gpt

open Wasm LeanExe.Pipeline LeanExe.IR LeanExe.Runtime Demos.Gpt.Exact

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
  have hReads : ∀ r ∈ Represent.reads store (stepArgs pc P tokens[p]! layers nh dh f eps)
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
        heap'.Owned final r (((Demos.Gpt.forward tokens W.wte W.wpe W.g1 W.b1 W.wq W.bq W.wk W.bk W.wv W.bv W.wo W.bo W.g2 W.b2 W.wfc W.bfc W.wproj
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

end Demos.Gpt
