import Project.EulerGridStep.FieldMemory

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Copy progress retains the input, array header, other store fields and outside bytes. -/
structure CopyState (initial : Store Unit) (source target : UInt64)
    (input output : Array UInt64) (current : Store Unit) (index : Nat) : Prop where
  pages : current.mem.pages = initial.mem.pages
  frame : { current with mem := initial.mem } = initial
  inputAt : UInt64Array.At current source input
  outputAt : UInt64Array.At current target output
  size : output.size = input.size
  copied : ∀ j < index, output[j]! = input[j]!
  outside : ∀ address, address < target.toNat + 8 ∨
      target.toNat + 8 * (input.size + 1) ≤ address →
    current.mem.bytes address = initial.mem.bytes address

theorem copyState_initial (initial : Store Unit) (source target : UInt64)
    (input output : Array UInt64) (hInput : UInt64Array.At initial source input)
    (hOutput : UInt64Array.At initial target output) (hSize : output.size = input.size) :
    CopyState initial source target input output initial 0 := by
  exact ⟨rfl, rfl, hInput, hOutput, hSize, by omega, by intros; rfl⟩

theorem copyState_step (initial current : Store Unit) (source target : UInt64)
    (input output : Array UInt64) (index : Nat)
    (h : CopyState initial source target input output current index)
    (hi : index < input.size)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (input.size + 1) ≤ source.toNat) :
    CopyState initial source target input (output.set! index input[index]!)
      (writeWord current target index input[index]!) (index + 1) := by
  have hSize := h.size
  have hOutputIndex : index < output.size := by omega
  refine ⟨(writeWord_pages _ _ _ _).trans h.pages, ?_, ?_,
    writeWord_array current target output index input[index]! h.outputAt hOutputIndex,
    by simpa using h.size, ?_, ?_⟩
  · exact h.frame
  · apply writeWord_preserves_array current source target input output index input[index]!
      h.inputAt h.outputAt hOutputIndex
    simpa [h.size] using hSeparate
  · intro j hj
    by_cases heq : j = index
    · subst j
      exact Array.getElem!_set!_self _ _ _ hOutputIndex
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm heq)]
      exact h.copied j (by omega)
  · intro address hOutside
    rw [writeWord_bytes_outside current target output index input[index]!
      h.outputAt hOutputIndex address (by omega)]
    exact h.outside address hOutside

theorem copyState_complete (initial current : Store Unit) (source target : UInt64)
    (input output : Array UInt64)
    (h : CopyState initial source target input output current input.size) :
    UInt64Array.At current target input := by
  have hEqual : output = input := by
    apply Array.ext h.size
    intro index ho hi
    simpa [ho, hi] using h.copied index hi
  simpa only [hEqual] using h.outputAt

#print axioms copyState_step
#print axioms copyState_complete
end Project.EulerGridStep.Execution
