import Project.EulerGridStep.FieldMemory

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- A logical array survives any store change preserving its bytes and available pages. -/
theorem arrayAt_of_byte_frame (initial current : Store Unit) (pointer : UInt64)
    (input : Array UInt64) (hInput : UInt64Array.At initial pointer input)
    (hPages : initial.mem.pages ≤ current.mem.pages)
    (hFrame : ∀ address, pointer.toNat ≤ address →
      address < pointer.toNat + 8 * (input.size + 1) →
      current.mem.bytes address = initial.mem.bytes address) :
    UInt64Array.At current pointer input := by
  have hRead (word : Nat) (hw : word < input.size + 1) :
      current.mem.read64 (UInt64Array.wordAddress pointer word) =
        initial.mem.read64 (UInt64Array.wordAddress pointer word) := by
    apply Memory.read64_congr
    intro byte hb
    apply hFrame
    · rw [UInt64Array.wordAddress_toNat hInput.1 hw]
      omega
    · rw [UInt64Array.wordAddress_toNat hInput.1 hw]
      omega
  refine ⟨hInput.1, hInput.2.1.trans (Nat.mul_le_mul_right 65536 hPages), ?_, ?_⟩
  · have h := hRead 0 (by omega)
    simpa [UInt64Array.wordAddress, hInput.lengthRead] using h
  · intro index hi
    exact (hRead (index + 1) (by omega)).trans (hInput.elementRead index hi)

#print axioms arrayAt_of_byte_frame
end Project.EulerGridStep.Execution
