import Project.EulerGridStep.FieldMemory

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Existing payload contents of an allocated region, before its length is initialized. -/
def payloadSnapshot (initial : Store Unit) (pointer : UInt64) (count : Nat) : Array UInt64 :=
  Array.ofFn fun index : Fin count =>
    initial.mem.read64 (UInt64Array.wordAddress pointer (index.val + 1))

def writeLength (initial : Store Unit) (pointer : UInt64) (count : Nat) : Store Unit :=
  { initial with mem := initial.mem.write64 pointer.toUInt32 (UInt64.ofNat count) }

/-- Initializing the length establishes a logical array without assuming zeroed payload bytes. -/
theorem writeLength_array (initial : Store Unit) (pointer : UInt64) (count : Nat)
    (hFit32 : pointer.toNat + 8 * (count + 1) ≤ 4294967296)
    (hFitMemory : pointer.toNat + 8 * (count + 1) ≤ initial.mem.pages * 65536) :
    UInt64Array.At (writeLength initial pointer count) pointer
      (payloadSnapshot initial pointer count) := by
  have hPointer : pointer.toUInt32.toNat = pointer.toNat := by
    simpa [UInt64Array.wordAddress] using
      UInt64Array.wordAddress_toNat hFit32 (by omega : 0 < count + 1)
  refine ⟨by simpa [payloadSnapshot] using hFit32,
    by simpa [payloadSnapshot, writeLength, Mem.write64_pages] using hFitMemory, ?_, ?_⟩
  · simp [writeLength, payloadSnapshot, read64_write64_exact, -Mem.read64_write64_same]
  · intro index hi
    have hIndex : index < count := by simpa [payloadSnapshot] using hi
    have hAddress := UInt64Array.wordAddress_toNat hFit32 (by omega : index + 1 < count + 1)
    have hRead : (writeLength initial pointer count).mem.read64
        (UInt64Array.wordAddress pointer (index + 1)) =
        initial.mem.read64 (UInt64Array.wordAddress pointer (index + 1)) := by
      apply Memory.read64_write64_disjoint
      right
      rw [hPointer, hAddress]
      omega
    simpa [payloadSnapshot, UInt64Array.wordAddress] using hRead

theorem writeLength_preserves_array (initial : Store Unit) (source target : UInt64)
    (input : Array UInt64) (count : Nat) (hInput : UInt64Array.At initial source input)
    (hFit32 : target.toNat + 8 * (count + 1) ≤ 4294967296)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (count + 1) ≤ source.toNat) :
    UInt64Array.At (writeLength initial target count) source input := by
  have hTarget : target.toUInt32.toNat = target.toNat := by
    simpa [UInt64Array.wordAddress] using
      UInt64Array.wordAddress_toNat hFit32 (by omega : 0 < count + 1)
  refine ⟨hInput.1, by simpa [writeLength, Mem.write64_pages] using hInput.2.1, ?_, ?_⟩
  · rw [writeLength, Memory.read64_write64_disjoint]
    · exact hInput.lengthRead
    · rw [hTarget, hInput.pointerAddress_toNat]
      omega
  · intro index hi
    rw [writeLength, Memory.read64_write64_disjoint]
    · exact hInput.elementRead index hi
    · rw [hTarget, hInput.elementAddress_toNat index hi]
      omega

theorem writeLength_bytes_outside (initial : Store Unit) (target : UInt64) (count address : Nat)
    (hFit32 : target.toNat + 8 * (count + 1) ≤ 4294967296)
    (hOutside : address < target.toNat ∨ target.toNat + 8 ≤ address) :
    (writeLength initial target count).mem.bytes address = initial.mem.bytes address := by
  apply Memory.write64_bytes_outside
  have hTarget : target.toUInt32.toNat = target.toNat := by
    simpa [UInt64Array.wordAddress] using
      UInt64Array.wordAddress_toNat hFit32 (by omega : 0 < count + 1)
  rwa [hTarget]

#print axioms writeLength_array
#print axioms writeLength_preserves_array
#print axioms writeLength_bytes_outside
end Project.EulerGridStep.Execution
