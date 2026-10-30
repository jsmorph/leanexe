import Demos.Gpt.Host
import Demos.Gpt.Verified

/-! The generation as the host runs it, on the verified compiler's module of GPT-2.  The host
calls `step` once per token, each time handing over the cache that the previous call returned,
which `step` consumes, and calls `scores` on the last cache.  `Generating heap store` describes a
store between these calls, with `heap` the allocator's state.  `generating_start` gives it for the
empty cache, `generating_step` shows that `step` gives it for one more token, and
`generating_scores` shows that `scores` then returns row `p` of `forward` and leaves a store of
the generation.  `generating_step` and `generating_scores` rest on the generated
`compiled.step.implements` and `compiled.scores.implements`, which allow a stop at `unreachable`.
`generating_step_trapFree` and `generating_scores_trapFree` rest on the generated `trapFree`
theorems: from a store in which `top` can rise by the call's generated bound within the memory
cap, the call returns without a trap, keeps the memory caps, and raises `top` by at most that
bound, so that `Heap.Within.after` gives the room for the next call. -/

namespace Demos.Gpt.Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime Demos.Gpt.Exact

/-- The argument tuple of `step`: the cache, which `step` consumes, the weights of the
embeddings and of the blocks, the token, the dimensions, and `eps`. -/
abbrev StepInput : Type :=
  Moved (Array Float) × Array Float × Array Float × Array Float × Array Float × Array Float ×
    Array Float × Array Float × Array Float × Array Float × Array Float × Array Float ×
    Array Float × Array Float × Array Float × Array Float × Array Float × Array Float ×
    Array Float × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × Float

/-- The argument tuple of `scores`: the cache, the token embeddings, the final layer norm's gain
and bias, the dimensions, and `eps`. -/
abbrev ScoresInput : Type :=
  Array Float × Array Float × Array Float × Array Float × UInt64 × UInt64 × UInt64 × UInt64 ×
    Float

/-- The arguments of `step` on token `p`, with the cache of the first `p` tokens. -/
abbrev stepInput (W : Weights) (tokens : Array UInt64) (layers nh dh f : UInt64) (eps : Float)
    (p : Nat) : StepInput :=
  (⟨W.cache tokens layers nh dh f eps p⟩, W.wte, W.wpe, W.g1, W.b1, W.wq, W.bq, W.wk, W.bk, W.wv,
    W.bv, W.wo, W.bo, W.g2, W.b2, W.wfc, W.bfc, W.wproj, W.bproj, tokens[p]!, layers, nh, dh, f,
    eps)

/-- The arguments of `scores` on the cache of the first `p` tokens. -/
abbrev scoresInput (W : Weights) (tokens : Array UInt64) (layers nh dh f vocab : UInt64)
    (eps : Float) (p : Nat) : ScoresInput :=
  (W.cache tokens layers nh dh f eps p, W.wte, W.gf, W.bf, layers, nh, dh, vocab, eps)

/-- A store between the calls of a generation, with `heap` the allocator's state: the allocator
invariant holds, the memory's cap is at most 65,535 pages, every weight array is borrowed at its
pointer and lies apart from the block of the object at `pc`, and the object at `pc` is owned and
holds the cache of the first `p` tokens. -/
def Generating (heap : Heap) (store : Store Unit) (W : Weights) (P : Pointers)
    (tokens : Array UInt64) (layers nh dh f : UInt64) (eps : Float) (pc : UInt64) (p : Nat) :
    Prop :=
  heap.At store ∧ store.memoryCap compiled.module 0 ≤ 65535 ∧
    (∀ w ∈ W.pairs P, heap.Borrowed store w.1 (w.2.map Float.toBits) ∧
      regionsDisjoint (w.1.toNat, 8 * (w.2.size + 1)) (pc.toNat - 48, 48 + capacityAt store pc)) ∧
    heap.Owned store pc ((W.cache tokens layers nh dh f eps p).map Float.toBits)

/-- The host's starting store: the weights borrowed, and an owned empty array at `pc` apart
from them. -/
theorem generating_start {heap : Heap} {store : Store Unit} {W : Weights} {P : Pointers}
    {tokens : Array UInt64} {layers nh dh f : UInt64} {eps : Float} {pc : UInt64}
    (hAt : heap.At store) (hCap : store.memoryCap compiled.module 0 ≤ 65535)
    (hW : ∀ w ∈ W.pairs P, heap.Borrowed store w.1 (w.2.map Float.toBits) ∧
      regionsDisjoint (w.1.toNat, 8 * (w.2.size + 1)) (pc.toNat - 48, 48 + capacityAt store pc))
    (hC : heap.Owned store pc #[]) :
    Generating heap store W P tokens layers nh dh f eps pc 0 :=
  ⟨hAt, hCap, hW, by simpa [Weights.cache, cacheAfter] using hC⟩

/-- A theorem of the form `ImplementsA` for function 41, whose function `g` gives the cache of the
first `p + 1` tokens, gives the step of the generation: from a store of the generation after `p`
tokens and with `Pre`, the call on token `p` consumes the cache at `pc` and, when it returns,
returns the address `pc'` of a cache in a store of the generation after `p + 1` tokens, keeps the
memory caps, and meets `Post`. -/
theorem step_runs {aborts : Bool} {g : StepInput → Array Float}
    {Pre : StepInput → Heap → Store Unit → Prop}
    {Post : StepInput → Heap → Store Unit → Heap → Store Unit → Prop} {heap : Heap}
    {store : Store Unit} {W : Weights} {P : Pointers} {tokens : Array UInt64}
    {layers nh dh f : UInt64} {eps : Float} {pc : UInt64} {p : Nat}
    (hI : ImplementsA aborts compiled.module 41 g Pre Post) (env : HostEnv Unit)
    (h : Generating heap store W P tokens layers nh dh f eps pc p)
    (hg : g (stepInput W tokens layers nh dh f eps p) = W.cache tokens layers nh dh f eps (p + 1))
    (hPre : Pre (stepInput W tokens layers nh dh f eps p) heap store) :
    Runs aborts env compiled.module 41 store (stepArgs pc P tokens[p]! layers nh dh f eps).reverse
      fun final values => ∃ pc', values = [.i64 pc'] ∧ ∃ heap',
        Generating heap' final W P tokens layers nh dh f eps pc' (p + 1) ∧
        final.memoryCaps = store.memoryCaps ∧
        Post (stepInput W tokens layers nh dh f eps p) heap store heap' final := by
  obtain ⟨hAt, hCap, hW, hC⟩ := h
  have b : ∀ q a, (q, a) ∈ W.pairs P → heap.Borrowed store q (a.map Float.toBits) :=
    fun q a h => (hW _ h).1
  have hApart : ∀ w ∈ W.pairs P,
      Apart store [pc] (w.1.toNat, 8 * ((w.2.map Float.toBits).size + 1)) := fun w hw q hq => by
    rw [List.mem_singleton] at hq
    subst hq
    rw [Array.size_map]
    exact (hW w hw).2
  have hReads : ∀ r ∈ Represent.reads store (stepArgs pc P tokens[p]! layers nh dh f eps)
      (stepInput W tokens layers nh dh f eps p), Apart store [pc] r := by
    rw [stepInput, step_reads]
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact hApart w (List.mem_of_mem_take hw)
  refine (hI env store heap (stepArgs pc P tokens[p]! layers nh dh f eps)
    (stepInput W tokens layers nh dh f eps p) hAt hPre
    ⟨[.i64 pc], _, rfl, ⟨pc, rfl, hC⟩, [.i64 P.wte], _, rfl,
      ⟨P.wte, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wpe], _, rfl,
      ⟨P.wpe, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.g1], _, rfl,
      ⟨P.g1, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.b1], _, rfl,
      ⟨P.b1, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wq], _, rfl,
      ⟨P.wq, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bq], _, rfl,
      ⟨P.bq, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wk], _, rfl,
      ⟨P.wk, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bk], _, rfl,
      ⟨P.bk, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wv], _, rfl,
      ⟨P.wv, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bv], _, rfl,
      ⟨P.bv, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wo], _, rfl,
      ⟨P.wo, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bo], _, rfl,
      ⟨P.bo, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.g2], _, rfl,
      ⟨P.g2, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.b2], _, rfl,
      ⟨P.b2, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wfc], _, rfl,
      ⟨P.wfc, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bfc], _, rfl,
      ⟨P.bfc, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.wproj], _, rfl,
      ⟨P.wproj, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bproj], _, rfl,
      ⟨P.bproj, rfl, b _ _ (by simp [Weights.pairs])⟩, rfl⟩
    ⟨List.pairwise_singleton _ _, hReads⟩ hCap).mono ?_
  rintro final values ⟨heap', hAt', ⟨pc', hValues, hNew⟩, hCaps, hRegion, hPost⟩
  have hValues' : values = [.i64 pc'] := by
    rw [← List.reverse_reverse values, hValues]; rfl
  refine ⟨pc', hValues', heap', ⟨hAt', memoryCap_le_of_caps hCaps hCap, fun w hw => ⟨?_, ?_⟩,
    hg ▸ hNew⟩, hCaps, hPost⟩
  · obtain ⟨hBytes, hReg, -⟩ := hRegion _ (hW w hw).1.region (by simp) (hApart w hw)
    exact (hW w hw).1.keepIn hAt' hBytes hReg
  · have hDisjoint := (hRegion _ (hW w hw).1.region (by simp) (hApart w hw)).2.2
    rw [hValues] at hDisjoint
    have h := Represent.outside_float.mp hDisjoint
    rw [Array.size_map] at h
    exact h

/-- A theorem of the form `ImplementsA` for function 42 gives the scores of the generation: from a
store of the generation after `p` tokens and with `Pre`, the call of `scores` on the cache at `pc`,
when it returns, returns the address `r` of an owned array that holds the result of `g` and leaves
a store of the generation after `p` tokens, with the same memory caps, that meets `Post`. -/
theorem scores_runs {aborts : Bool} {g : ScoresInput → Array Float}
    {Pre : ScoresInput → Heap → Store Unit → Prop}
    {Post : ScoresInput → Heap → Store Unit → Heap → Store Unit → Prop} {heap : Heap}
    {store : Store Unit} {W : Weights} {P : Pointers} {tokens : Array UInt64}
    {layers nh dh f vocab : UInt64} {eps : Float} {pc : UInt64} {p : Nat}
    (hI : ImplementsA aborts compiled.module 42 g Pre Post) (env : HostEnv Unit)
    (h : Generating heap store W P tokens layers nh dh f eps pc p)
    (hPre : Pre (scoresInput W tokens layers nh dh f vocab eps p) heap store) :
    Runs aborts env compiled.module 42 store (scoresArgs pc P layers nh dh vocab eps).reverse
      fun final values => ∃ r, values = [.i64 r] ∧ ∃ heap',
        heap'.Owned final r
          ((g (scoresInput W tokens layers nh dh f vocab eps p)).map Float.toBits) ∧
        Generating heap' final W P tokens layers nh dh f eps pc p ∧
        final.memoryCaps = store.memoryCaps ∧
        Post (scoresInput W tokens layers nh dh f vocab eps p) heap store heap' final := by
  obtain ⟨hAt, hCap, hW, hC⟩ := h
  have b : ∀ q a, (q, a) ∈ W.pairs P → heap.Borrowed store q (a.map Float.toBits) :=
    fun q a h => (hW _ h).1
  refine (hI env store heap (scoresArgs pc P layers nh dh vocab eps)
    (scoresInput W tokens layers nh dh f vocab eps p) hAt hPre
    ⟨[.i64 pc], _, rfl, ⟨pc, rfl, hC.borrowed⟩, [.i64 P.wte], _, rfl,
      ⟨P.wte, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.gf], _, rfl,
      ⟨P.gf, rfl, b _ _ (by simp [Weights.pairs])⟩, [.i64 P.bf], _, rfl,
      ⟨P.bf, rfl, b _ _ (by simp [Weights.pairs])⟩, rfl⟩
    Separate.nil hCap).mono ?_
  rintro final values ⟨heap', hAt', ⟨r, hValues, hOwned⟩, hCaps, hRegion, hPost⟩
  have hKeep : ∀ q, heap.Region q → 0 < q.2 →
      (∀ a, q.1 ≤ a → a < q.1 + q.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region q :=
    fun q hq hpos => ⟨(hRegion q hq hpos Apart.nil).1, (hRegion q hq hpos Apart.nil).2.1⟩
  have hBlock : 0 < (LeanExe.Pipeline.block store pc).2 := by
    simp only [LeanExe.Pipeline.block]; omega
  obtain ⟨hC', hCapacity⟩ :=
    hC.keepIn hAt' (hKeep _ hC.region hBlock).1 (hKeep _ hC.region hBlock).2
  refine ⟨r, by rw [← List.reverse_reverse values, hValues]; rfl, heap', hOwned,
    ⟨hAt', memoryCap_le_of_caps hCaps hCap, fun w hw => ⟨?_, ?_⟩, hC'⟩, hCaps, hPost⟩
  · obtain ⟨hBytes, hReg⟩ := hKeep _ (hW w hw).1.region (by simp)
    exact (hW w hw).1.keepIn hAt' hBytes hReg
  · rw [hCapacity]
    exact (hW w hw).2

/-- `step` on token `p` consumes the cache at `pc` and aborts or returns the cache of the
first `p + 1` tokens, leaving a store of the generation after `p + 1` tokens. -/
theorem generating_step {heap : Heap} {store : Store Unit} {W : Weights} {P : Pointers}
    {tokens : Array UInt64} {layers nh dh f : UInt64} {eps : Float} {pc : UInt64} {p : Nat}
    (env : HostEnv Unit) (h : Generating heap store W P tokens layers nh dh f eps pc p) :
    ReturnsOrAborts env compiled.module 41 store
      (stepArgs pc P tokens[p]! layers nh dh f eps).reverse
      fun final values => ∃ pc', values = [.i64 pc'] ∧ ∃ heap',
        Generating heap' final W P tokens layers nh dh f eps pc' (p + 1) :=
  (step_runs compiled.step.implements env h rfl trivial).mono
    fun _ _ ⟨pc', hv, heap', hG, _⟩ => ⟨pc', hv, heap', hG⟩

/-- `step` on token `p`, from a store of the generation in which `top` can rise by the generated
bound of `step` within the memory cap, consumes the cache at `pc` and returns without a trap the
cache of the first `p + 1` tokens.  It leaves a store of the generation after `p + 1` tokens with
the same memory caps, and `top` rises by at most the bound. -/
theorem generating_step_trapFree {heap : Heap} {store : Store Unit} {W : Weights}
    {P : Pointers} {tokens : Array UInt64} {layers nh dh f : UInt64} {eps : Float}
    {pc : UInt64} {p : Nat} (env : HostEnv Unit)
    (h : Generating heap store W P tokens layers nh dh f eps pc p)
    (hroom : heap.Within store compiled.module
      (compiled.step.bound (stepInput W tokens layers nh dh f eps p))) :
    Runs false env compiled.module 41 store (stepArgs pc P tokens[p]! layers nh dh f eps).reverse
      fun final values => ∃ pc', values = [.i64 pc'] ∧ ∃ heap',
        Generating heap' final W P tokens layers nh dh f eps pc' (p + 1) ∧
        final.memoryCaps = store.memoryCaps ∧
        heap'.top.toNat ≤
          heap.top.toNat + compiled.step.bound (stepInput W tokens layers nh dh f eps p) :=
  step_runs compiled.step.trapFree env h rfl hroom

/-- `scores` on the cache of the first `p + 1` tokens aborts or returns a new array that holds
row `p` of `forward` on any `T > p` tokens, under the bounds of `steps_exact`, and leaves a store
of the generation after `p + 1` tokens. -/
theorem generating_scores {heap : Heap} {store : Store Unit} {W : Weights} {P : Pointers}
    {tokens : Array UInt64} {layers T nh dh f vocab : UInt64} {eps : Float} {pc : UInt64}
    {p : Nat} (env : HostEnv Unit)
    (h : Generating heap store W P tokens layers nh dh f eps pc (p + 1))
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hn0 : 0 < nh.toNat) (hdh0 : 0 < dh.toNat) (hf : f.toNat < 2 ^ 32)
    (hv : vocab.toNat < 2 ^ 32) (hL : layers.toNat < 2 ^ 16)
    (hall : T.toNat * ((2 * layers.toNat + 1) * (nh.toNat * dh.toNat)) < 2 ^ 32) :
    ReturnsOrAborts env compiled.module 42 store (scoresArgs pc P layers nh dh vocab eps).reverse
      fun final values => ∃ r, values = [.i64 r] ∧ ∃ heap',
        heap'.Owned final r ((forward tokens W.wte W.wpe W.g1 W.b1 W.wq W.bq W.wk W.bk W.wv W.bv
          W.wo W.bo W.g2 W.b2 W.wfc W.bfc W.wproj W.bproj W.gf W.bf layers T nh dh f vocab
          eps).extract (p * vocab.toNat) ((p + 1) * vocab.toNat) |>.map Float.toBits) ∧
        Generating heap' final W P tokens layers nh dh f eps pc (p + 1) := by
  rw [← steps_exact hp hT hn hdh hn0 hdh0 hf hv hL hall]
  exact (scores_runs compiled.scores.implements env h trivial).mono
    fun _ _ ⟨r, hv, heap', hOwned, hG, _⟩ => ⟨r, hv, heap', hOwned, hG⟩

/-- `scores` on the cache of the first `p + 1` tokens, from a store of the generation in which
`top` can rise by the generated bound of `scores` within the memory cap, returns without a trap a
new array that holds row `p` of `forward` on any `T > p` tokens, under the bounds of
`steps_exact`.  It leaves a store of the generation after `p + 1` tokens with the same memory
caps, and `top` rises by at most the bound. -/
theorem generating_scores_trapFree {heap : Heap} {store : Store Unit} {W : Weights}
    {P : Pointers} {tokens : Array UInt64} {layers T nh dh f vocab : UInt64} {eps : Float}
    {pc : UInt64} {p : Nat} (env : HostEnv Unit)
    (h : Generating heap store W P tokens layers nh dh f eps pc (p + 1))
    (hroom : heap.Within store compiled.module
      (compiled.scores.bound (scoresInput W tokens layers nh dh f vocab eps (p + 1))))
    (hp : p < T.toNat) (hT : T.toNat < 2 ^ 16) (hn : nh.toNat < 2 ^ 16) (hdh : dh.toNat < 2 ^ 16)
    (hn0 : 0 < nh.toNat) (hdh0 : 0 < dh.toNat) (hf : f.toNat < 2 ^ 32)
    (hv : vocab.toNat < 2 ^ 32) (hL : layers.toNat < 2 ^ 16)
    (hall : T.toNat * ((2 * layers.toNat + 1) * (nh.toNat * dh.toNat)) < 2 ^ 32) :
    Runs false env compiled.module 42 store (scoresArgs pc P layers nh dh vocab eps).reverse
      fun final values => ∃ r, values = [.i64 r] ∧ ∃ heap',
        heap'.Owned final r ((forward tokens W.wte W.wpe W.g1 W.b1 W.wq W.bq W.wk W.bk W.wv W.bv
          W.wo W.bo W.g2 W.b2 W.wfc W.bfc W.wproj W.bproj W.gf W.bf layers T nh dh f vocab
          eps).extract (p * vocab.toNat) ((p + 1) * vocab.toNat) |>.map Float.toBits) ∧
        Generating heap' final W P tokens layers nh dh f eps pc (p + 1) ∧
        final.memoryCaps = store.memoryCaps ∧
        heap'.top.toNat ≤ heap.top.toNat +
          compiled.scores.bound (scoresInput W tokens layers nh dh f vocab eps (p + 1)) := by
  rw [← steps_exact hp hT hn hdh hn0 hdh0 hf hv hL hall]
  exact scores_runs compiled.scores.trapFree env h hroom

#print axioms generating_start
#print axioms step_runs
#print axioms scores_runs
#print axioms generating_step
#print axioms generating_step_trapFree
#print axioms generating_scores
#print axioms generating_scores_trapFree

end Demos.Gpt.Verified
