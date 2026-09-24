import Project.EulerGridStep.BufferState

namespace Project.EulerGridStep.Execution
open Wasm

/-- Move the last clone to the result slot and the old result to the free-list head. -/
def acceptedPoolSlot (i : Nat) : Nat := if i = 0 then 6 else i - 1

/-- Rejection clones only into the free-list head, then releases the old result. -/
def rejectedPoolSlot (i : Nat) : Nat := if i = 0 then 1 else if i = 1 then 0 else i

theorem acceptedPoolSlot_bound {i : Nat} (hi : i ≤ 6) : acceptedPoolSlot i ≤ 6 := by
  unfold acceptedPoolSlot
  split <;> omega

theorem acceptedPoolSlot_injective {i j : Nat} (hi : i ≤ 6) (hj : j ≤ 6)
    (h : acceptedPoolSlot i = acceptedPoolSlot j) : i = j := by
  unfold acceptedPoolSlot at h
  split at h <;> split at h <;> omega

theorem rejectedPoolSlot_bound {i : Nat} (hi : i ≤ 6) : rejectedPoolSlot i ≤ 6 := by
  unfold rejectedPoolSlot
  split <;> (try split) <;> omega

theorem rejectedPoolSlot_injective {i j : Nat}
    (h : rejectedPoolSlot i = rejectedPoolSlot j) : i = j := by
  unfold rejectedPoolSlot at h
  split at h <;> split at h <;> (try split at h) <;> (try split at h) <;> omega

/-- Geometry shared by the current result and all six free buffers. -/
structure RecycledGeometry (roots : Nat → UInt64) (pointer initialRoot : UInt64)
    (inputCount outputCount : Nat) : Prop where
  separate : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) outputCount (roots b) outputCount
  inputSeparate : ∀ a ≤ 6, ObjectsSeparate (roots a) outputCount pointer inputCount
  initialSeparate : ∀ a ≤ 6, ObjectsSeparate (roots a) outputCount initialRoot outputCount

/-- A current result and six reusable buffers; all seven may be permuted between iterations. -/
structure RecycledPool (current : Store Unit) (roots : Nat → UInt64)
    (pointer initialRoot : UInt64) (input output : Array UInt64) (allocs releases frees : UInt64)
    : Prop extends RecycledGeometry roots pointer initialRoot input.size output.size where
  buffers : BufferState current output.size [⟨roots 0, output⟩]
    [roots 1, roots 2, roots 3, roots 4, roots 5, roots 6] allocs releases frees

/-- Slot permutations retain all geometric separation facts, independent of array contents. -/
theorem recycled_separation_relabel (roots : Nat → UInt64) (slot : Nat → Nat) (count : Nat)
    (hBound : ∀ i ≤ 6, slot i ≤ 6)
    (hInjective : ∀ i ≤ 6, ∀ j ≤ 6, slot i = slot j → i = j)
    (hSeparate : ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots a) count (roots b) count) :
    ∀ a ≤ 6, ∀ b ≤ 6, a ≠ b → ObjectsSeparate (roots (slot a)) count (roots (slot b)) count := by
  intro a ha b hb hab
  exact hSeparate _ (hBound a ha) _ (hBound b hb) (fun h => hab (hInjective a ha b hb h))

theorem RecycledGeometry.relabel {roots : Nat → UInt64} {pointer initialRoot : UInt64}
    {inputCount outputCount : Nat} (h : RecycledGeometry roots pointer initialRoot inputCount outputCount)
    (slot : Nat → Nat) (hBound : ∀ i ≤ 6, slot i ≤ 6)
    (hInjective : ∀ i ≤ 6, ∀ j ≤ 6, slot i = slot j → i = j) :
    RecycledGeometry (roots ∘ slot) pointer initialRoot inputCount outputCount :=
  ⟨recycled_separation_relabel roots slot outputCount hBound hInjective h.separate,
    fun i hi => h.inputSeparate _ (hBound i hi),
    fun i hi => h.initialSeparate _ (hBound i hi)⟩

#print axioms acceptedPoolSlot_injective
#print axioms rejectedPoolSlot_injective
#print axioms recycled_separation_relabel
end Project.EulerGridStep.Execution
