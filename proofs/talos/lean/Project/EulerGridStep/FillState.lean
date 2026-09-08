import Project.EulerGridStep.FieldMemory

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A constant-filled prefix with the exact remaining store and outside payload bytes preserved. -/
structure FillState (initial : Store Unit) (target value : UInt64) (original : Array UInt64)
    (current : Store Unit) (output : Array UInt64) (index : Nat) : Prop where
  pages : current.mem.pages = initial.mem.pages
  frame : { current with mem := initial.mem } = initial
  size : output.size = original.size
  arrayAt : UInt64Array.At current target output
  filled : ∀ i < index, i < original.size → output[i]! = value
  outside : ∀ address, address < target.toNat + 8 ∨ target.toNat + 8 * (original.size + 1) ≤ address →
    current.mem.bytes address = initial.mem.bytes address

theorem fillState_initial (initial : Store Unit) (target value : UInt64) (original : Array UInt64)
    (hArray : UInt64Array.At initial target original) :
    FillState initial target value original initial original 0 := by
  exact ⟨rfl, by cases initial; rfl, rfl, hArray, by intro i hi; omega, by intros; rfl⟩

/-- One in-bounds scalar store extends the initialized prefix by one word. -/
theorem fillState_step (initial current : Store Unit) (target value : UInt64)
    (original output : Array UInt64) (index : Nat)
    (hState : FillState initial target value original current output index) (hi : index < original.size) :
    FillState initial target value original (writeWord current target index value)
      (output.set! index value) (index + 1) := by
  have hSize := hState.size
  have ho : index < output.size := by omega
  refine ⟨(writeWord_pages current target index value).trans hState.pages, ?_, ?_,
    writeWord_array current target output index value hState.arrayAt ho, ?_, ?_⟩
  · exact hState.frame
  · simpa using hSize
  · intro i hIndex hOriginal
    by_cases heq : i = index
    · subst i
      exact Array.getElem!_set!_self output index value ho
    · rw [Array.getElem!_set!_ne output index i value (Ne.symm heq)]
      exact hState.filled i (by omega) hOriginal
  · intro address hOutside
    rw [writeWord_bytes_outside current target output index value hState.arrayAt ho address (by omega)]
    exact hState.outside address hOutside

/-- Filling the complete prefix yields exactly the replicated constant array. -/
theorem FillState.complete {initial current : Store Unit} {target value : UInt64}
    {original output : Array UInt64}
    (hState : FillState initial target value original current output original.size) :
    output = Array.replicate original.size value := by
  have hSize := hState.size
  apply Array.ext (by simpa using hSize)
  intro i hi hRep
  have hOriginal : i < original.size := by omega
  have h := hState.filled i hOriginal hOriginal
  simpa [hi] using h

#print axioms fillState_initial
#print axioms fillState_step
#print axioms FillState.complete
end Project.EulerGridStep.Execution
