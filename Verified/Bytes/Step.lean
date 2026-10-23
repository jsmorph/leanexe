import Verified.Bytes.Basic
import Verified.HeapStep

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def regions (store : Store Unit) (root : UInt64) : List (Nat × Nat) :=
  if root = 0 then [] else [block store root]

theorem Allocated.step {heap heap' : Heap} {store store' : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (h : Allocated heap store root bytes) (hStep : Step heap store keep heap' store' fresh)
    (hKeep : keep (block store root)) :
    (Allocated heap' store' root bytes ∧ capacityAt store' root = capacityAt store root) ∧
      ∀ b ∈ fresh, regionsDisjoint (block store root) b := by
  obtain ⟨hBytes, hRegion, hFresh⟩ := hStep.keeps _ h.region (by simp) hKeep
  refine ⟨h.frameIn ?_ hRegion, hFresh⟩
  intro a hl hh
  exact hBytes a hl (by have := h.object.base; omega)

theorem Rep.step {heap heap' : Heap} {store store' : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (h : Rep heap store root length bytes) (hStep : Step heap store keep heap' store' fresh)
    (hKeep : ∀ r ∈ regions store root, keep r) :
    Rep heap' store' root length bytes ∧ regions store' root = regions store root ∧
      ∀ r ∈ regions store root, ∀ b ∈ fresh, regionsDisjoint r b := by
  rcases h.buffer with hNull | hBuffer
  · obtain ⟨rfl, hEmpty⟩ := hNull
    exact ⟨⟨h.length_eq, Or.inl ⟨rfl, hEmpty⟩⟩, rfl, by simp [regions]⟩
  · have hNonzero := hBuffer.nonzero
    obtain ⟨⟨hBuffer', hCapacity⟩, hFresh⟩ :=
      hBuffer.step hStep (hKeep _ (by simp [regions, hNonzero]))
    refine ⟨⟨h.length_eq, Or.inr hBuffer'⟩, ?_, ?_⟩
    · simp only [regions, ite_eq_right hNonzero, block, hCapacity]
    · intro r hr b hb
      simp only [regions, ite_eq_right hNonzero, List.mem_singleton] at hr
      subst r
      exact hFresh b hb

end Verified.Bytes
