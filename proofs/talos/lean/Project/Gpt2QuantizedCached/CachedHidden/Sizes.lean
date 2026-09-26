import Project.Gpt2QuantizedCached.CachedHidden.Source

namespace Project.Gpt2QuantizedCached.CachedHidden
open LeanExe.Models.Gpt2.Quantized Project.ProofKit

def ValidState (count : Nat) (state : LayerState) : Prop :=
  (state.2.2 = 0 ∧ state.1.size = 3072 ∧ state.2.1.size = count * 6144) ∨
    (state.2.2 = 4 ∧ state.1 = .empty ∧ state.2.1.size ≤ count * 6144)

theorem resultState_valid (count : Nat) (updates : ByteArray) (result : HiddenResult)
    (hUpdates : updates.size = count * 6144)
    (hResult : (result.status = 0 ∧ result.hidden.size = 3072 ∧ result.cache.size = 6144) ∨
      (result.status = 4 ∧ result.hidden = .empty ∧ result.cache = .empty)) :
    ValidState (count + 1) (result.hidden, updates ++ result.cache, result.status) := by
  rcases hResult with ⟨hStatus, hHidden, hCache⟩ | ⟨hStatus, hHidden, hCache⟩
  · exact Or.inl ⟨hStatus, hHidden, by simp only [ByteArray.size_append, hUpdates, hCache]; omega⟩
  · exact Or.inr ⟨hStatus, hHidden, by simp only [ByteArray.size_append, hUpdates, hCache, ByteArray.size_empty]; omega⟩

theorem layerStep_zero (weights cache : ByteArray) (position count : Nat) (state : LayerState)
    (hZero : state.2.2 = 0) :
    layerStep weights cache position state count =
      ((cachedBlock weights state.1 cache count position).hidden,
       state.2.1 ++ (cachedBlock weights state.1 cache count position).cache,
       (cachedBlock weights state.1 cache count position).status) := by
  simp only [layerStep, hZero, beq_self_eq_true, ite_true]

theorem layerStep_nonzero (weights cache : ByteArray) (position count : Nat) (state : LayerState)
    (hNonzero : state.2.2 ≠ 0) : layerStep weights cache position state count = state := by
  simp only [layerStep, beq_iff_eq, hNonzero, ite_false]

theorem layerStep_valid (weights cache : ByteArray) (position count : Nat) (state : LayerState)
    (hState : ValidState count state) :
    ValidState (count + 1) (layerStep weights cache position state count) := by
  rcases hState with ⟨hZero, hHidden, hUpdates⟩ | ⟨hFour, hHidden, hUpdates⟩
  · rw [layerStep_zero weights cache position count state hZero]
    exact resultState_valid count state.2.1 _ hUpdates
      (CachedBlock.cachedBlock_sizes weights state.1 cache count position hHidden)
  · have hNonzero : state.2.2 ≠ 0 := by rw [hFour]; decide
    rw [layerStep_nonzero weights cache position count state hNonzero]
    exact Or.inr ⟨hFour, hHidden, hUpdates.trans (Nat.mul_le_mul_right 6144 (Nat.le_succ count))⟩

theorem embedding_size (weights : ByteArray) (token : UInt32) (position : Nat) :
    (embedding weights token position).size = 3072 := by
  rw [embedding, PackedSource.generate_size]

theorem layerPrefix_valid (weights cache : ByteArray) (token : UInt32) (position count : Nat) :
    ValidState count (layerPrefix weights cache token position count) := by
  induction count with
  | zero => exact Or.inl ⟨rfl, embedding_size weights token position, rfl⟩
  | succ count ih =>
    rw [layerPrefix_succ]
    exact layerStep_valid weights cache position count _ ih

theorem finished_sizes (cache : ByteArray) (state : LayerState) (hValid : ValidState 12 state) :
    let result : HiddenResult :=
      if state.2.2 != 0 then { status := state.2.2, hidden := .empty, cache := .empty }
      else { status := 0, hidden := state.1, cache := cache ++ state.2.1 }
    (result.status = 0 ∧ result.hidden.size = 3072 ∧ result.cache.size = cache.size + 73728) ∨
      (result.status = 4 ∧ result.hidden = .empty ∧ result.cache = .empty) := by
  rcases hValid with ⟨hZero, hHidden, hUpdates⟩ | ⟨hFour, hHidden, hUpdates⟩
  · simp only [hZero, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact Or.inl ⟨trivial, hHidden, by simp only [ByteArray.size_append, hUpdates]⟩
  · simp only [hFour, show ((4 : UInt64) != 0) = true from rfl, ite_true]
    exact Or.inr ⟨trivial, trivial, trivial⟩

def SizedResult (cacheSize : Nat) (result : HiddenResult) : Prop :=
  (result.status = 0 ∧ result.hidden.size = 3072 ∧ result.cache.size = cacheSize + 73728) ∨
    (result.status = 4 ∧ result.hidden = .empty ∧ result.cache = .empty)

theorem sized_of_finished (cache : ByteArray) (state : LayerState) (result : HiddenResult)
    (hEq : result = if state.2.2 != 0 then { status := state.2.2, hidden := .empty, cache := .empty }
      else { status := 0, hidden := state.1, cache := cache ++ state.2.1 })
    (hValid : ValidState 12 state) : SizedResult cache.size result := by
  rw [hEq]
  exact finished_sizes cache state hValid

theorem cachedHidden_sizes (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    SizedResult cache.size (cachedHidden weights cache token position) :=
  sized_of_finished cache (layerPrefix weights cache token position 12) _
    (cachedHidden_eq weights cache token position) (layerPrefix_valid weights cache token position 12)

#print axioms layerPrefix_valid
#print axioms cachedHidden_sizes
end Project.Gpt2QuantizedCached.CachedHidden
