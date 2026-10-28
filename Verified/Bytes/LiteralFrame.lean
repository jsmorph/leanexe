import Verified.Bytes.LiteralPool
import Verified.HeapStep
import LeanExe.ProofKit.ReleaseTree

namespace Verified.Bytes.LiteralPool

open Wasm LeanExe.Pipeline LeanExe.Runtime

def regions (pool : LiteralPool) : List (Nat × Nat) :=
  if pool.payload = [] then [] else [(pool.base, pool.payload.length)]

def Static (pool : LiteralPool) (heap : Heap) (store : Store Unit) : Prop :=
  pool.payload = [] ∨ pool.Valid store.mem ∧ heap.Region (pool.base, pool.payload.length)

theorem Static.empty (base : Nat) (heap : Heap) (store : Store Unit) :
    Static ⟨base, []⟩ heap store := Or.inl rfl

theorem Static.literal {pool : LiteralPool} {heap : Heap} {store : Store Unit}
    (h : pool.Static heap store) {bytes : Literal} {offset : Nat}
    (hOffset : literalOffset pool.values bytes = some offset) (hNonempty : bytes ≠ []) :
    At store.mem (UInt64.ofNat (pool.base + offset)) bytes.value ∧
      heap.Region ((UInt64.ofNat (pool.base + offset)).toNat, bytes.value.data.size) := by
  rcases h with hEmpty | ⟨hValid, hRegion⟩
  · have hBound := literalOffset_bound hOffset
    have hSize : pool.values.flatten.length = 0 := congrArg List.length hEmpty
    have hPositive : 0 < bytes.length := by cases bytes <;> simp_all
    omega
  · have hBounds := hValid.literal_bounds hOffset
    exact ⟨hValid.literal hOffset, hRegion.sub ⟨hBounds.1, hBounds.2⟩⟩

theorem Static.step {pool : LiteralPool} {heap heap' : Heap} {store store' : Store Unit}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (h : pool.Static heap store) (hStep : Step heap store keep heap' store' fresh)
    (hKeep : ∀ region ∈ pool.regions, keep region) :
    pool.Static heap' store' ∧
      ∀ region ∈ pool.regions, ∀ block ∈ fresh, regionsDisjoint region block := by
  by_cases hEmpty : pool.payload = []
  · exact ⟨Or.inl hEmpty, by simp [regions, hEmpty]⟩
  · obtain ⟨hValid, hRegion⟩ := h.resolve_left hEmpty
    have hPositive : 0 < pool.payload.length := by
      exact Nat.pos_of_ne_zero fun hLength => hEmpty (List.length_eq_zero_iff.mp hLength)
    obtain ⟨hBytes, hRegion', hFresh⟩ := hStep.keeps _ hRegion hPositive
      (hKeep _ (by simp [regions, hEmpty]))
    refine ⟨Or.inr ⟨hValid.frame ?_ hBytes, hRegion'⟩, ?_⟩
    · exact hRegion'.below.trans hStep.at_.top
    · intro region hRegion block hBlock
      simp only [regions, ite_eq_right hEmpty, List.mem_singleton] at hRegion
      subst region
      exact hFresh block hBlock

end Verified.Bytes.LiteralPool
