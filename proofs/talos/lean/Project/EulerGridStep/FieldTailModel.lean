import Project.EulerGridStep.HeaderMemory
import Project.EulerGridStep.CopyModel

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Exact logical field update, with source, store and allocation-boundary framing. -/
structure FieldWriteState (initial : Store Unit) (source target : UInt64)
    (input : Array UInt64) (index : Nat) (value : UInt64) (final : Store Unit) : Prop where
  pages : final.mem.pages = initial.mem.pages
  frame : { final with mem := initial.mem } = initial
  inputAt : UInt64Array.At final source input
  outputAt : UInt64Array.At final target (input.set! index value)
  outside : ∀ address, address < target.toNat ∨
      target.toNat + 8 * (input.size + 1) ≤ address →
    final.mem.bytes address = initial.mem.bytes address

theorem fieldWrite_after_copy (initial current : Store Unit) (source target : UInt64)
    (input output : Array UInt64) (index : Nat) (value : UInt64)
    (hi : index < input.size)
    (hCopy : CopyState (writeLength initial target input.size) source target input output
      current input.size)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (input.size + 1) ≤ source.toNat) :
    FieldWriteState initial source target input index value (writeWord current target index value) := by
  have hArray := copyState_complete _ _ _ _ _ _ hCopy
  refine ⟨?_, ?_, writeWord_preserves_array current source target input input index value
    hCopy.inputAt hArray hi hSeparate, writeWord_array current target input index value hArray hi, ?_⟩
  · simpa [writeWord_pages, writeLength, Mem.write64_pages] using hCopy.pages
  · exact congrArg (fun s : Store Unit => { s with mem := initial.mem }) hCopy.frame
  · intro address hOutside
    rw [writeWord_bytes_outside current target input index value hArray hi address (by omega)]
    rw [hCopy.outside address (by omega)]
    exact writeLength_bytes_outside initial target input.size address hArray.1 (by omega)

#print axioms fieldWrite_after_copy
end Project.EulerGridStep.Execution
