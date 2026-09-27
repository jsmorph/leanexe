import Project.EulerGridStep.WordRoundtrip

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- One payload-word store, with every non-memory component retained. -/
def writeWord (initial : Store Unit) (pointer : UInt64) (index : Nat)
    (value : UInt64) : Store Unit :=
  { initial with mem := initial.mem.write64 (UInt64Array.wordAddress pointer (index + 1)) value }

theorem writeWord_pages (initial : Store Unit) (pointer : UInt64) (index : Nat) (value : UInt64) :
    (writeWord initial pointer index value).mem.pages = initial.mem.pages := by
  simp [writeWord, Mem.write64_pages]

theorem writeWord_globals (initial : Store Unit) (pointer : UInt64) (index : Nat) (value : UInt64) :
    (writeWord initial pointer index value).globals = initial.globals := rfl

/-- The write leaves every byte outside the selected eight-byte word unchanged. -/
theorem writeWord_bytes_outside (initial : Store Unit) (pointer : UInt64)
    (input : Array UInt64) (index : Nat) (value : UInt64)
    (hArray : UInt64Array.At initial pointer input) (hi : index < input.size)
    (address : Nat)
    (hOutside : address < pointer.toNat + 8 * (index + 1) ∨
      pointer.toNat + 8 * (index + 1) + 8 ≤ address) :
    (writeWord initial pointer index value).mem.bytes address = initial.mem.bytes address := by
  apply Memory.write64_bytes_outside
  change address < ((pointer + UInt64.ofNat (8 * (index + 1))).toUInt32).toNat ∨
    ((pointer + UInt64.ofNat (8 * (index + 1))).toUInt32).toNat + 8 ≤ address
  rwa [hArray.elementAddress_toNat index hi]

/-- An in-bounds physical word store realizes the corresponding logical array update. -/
theorem writeWord_array (initial : Store Unit) (pointer : UInt64) (input : Array UInt64)
    (index : Nat) (value : UInt64) (hArray : UInt64Array.At initial pointer input)
    (hi : index < input.size) :
    UInt64Array.At (writeWord initial pointer index value) pointer (input.set! index value) := by
  have hWrite := hArray.elementAddress_toNat index hi
  have hHeader := hArray.pointerAddress_toNat
  have hHeaderRead : (writeWord initial pointer index value).mem.read64 pointer.toUInt32 =
      initial.mem.read64 pointer.toUInt32 := by
    apply Memory.read64_write64_disjoint
    left
    change pointer.toUInt32.toNat + 8 ≤
      ((pointer + UInt64.ofNat (8 * (index + 1))).toUInt32).toNat
    rw [hHeader, hWrite]
    omega
  refine ⟨by simpa using hArray.1, ?_, ?_, ?_⟩
  · simpa [writeWord_pages] using hArray.2.1
  · simpa [hHeaderRead] using hArray.lengthRead
  · intro readIndex hRead
    have hr : readIndex < input.size := by simpa using hRead
    by_cases heq : readIndex = index
    · subst readIndex
      simp [writeWord, UInt64Array.wordAddress, read64_write64_exact,
        -Mem.read64_write64_same]
    · have hReadAddress := hArray.elementAddress_toNat readIndex hr
      have hSeparate : (writeWord initial pointer index value).mem.read64
          (pointer + UInt64.ofNat (8 * (readIndex + 1))).toUInt32 = input[readIndex] := by
        rw [writeWord]
        rw [Memory.read64_write64_disjoint]
        · exact hArray.elementRead readIndex hr
        · change ((pointer + UInt64.ofNat (8 * (readIndex + 1))).toUInt32).toNat + 8 ≤
              ((pointer + UInt64.ofNat (8 * (index + 1))).toUInt32).toNat ∨
            ((pointer + UInt64.ofNat (8 * (index + 1))).toUInt32).toNat + 8 ≤
              ((pointer + UInt64.ofNat (8 * (readIndex + 1))).toUInt32).toNat
          rw [hReadAddress, hWrite]
          omega
      simpa [Array.getElem_setIfInBounds, hr, heq, Ne.symm heq] using hSeparate

/-- Writing a separate result buffer preserves the entire logical input array. -/
theorem writeWord_preserves_array (initial : Store Unit) (source target : UInt64)
    (input output : Array UInt64) (index : Nat) (value : UInt64)
    (hInput : UInt64Array.At initial source input)
    (hOutput : UInt64Array.At initial target output) (hi : index < output.size)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (output.size + 1) ≤ source.toNat) :
    UInt64Array.At (writeWord initial target index value) source input := by
  have hWrite := hOutput.elementAddress_toNat index hi
  refine ⟨hInput.1, ?_, ?_, ?_⟩
  · simpa [writeWord_pages] using hInput.2.1
  · rw [writeWord]
    rw [Memory.read64_write64_disjoint]
    · exact hInput.lengthRead
    · change source.toUInt32.toNat + 8 ≤
          ((target + UInt64.ofNat (8 * (index + 1))).toUInt32).toNat ∨
        ((target + UInt64.ofNat (8 * (index + 1))).toUInt32).toNat + 8 ≤ source.toUInt32.toNat
      rw [hInput.pointerAddress_toNat, hWrite]
      omega
  · intro readIndex hr
    rw [writeWord]
    rw [Memory.read64_write64_disjoint]
    · exact hInput.elementRead readIndex hr
    · change ((source + UInt64.ofNat (8 * (readIndex + 1))).toUInt32).toNat + 8 ≤
          ((target + UInt64.ofNat (8 * (index + 1))).toUInt32).toNat ∨
        ((target + UInt64.ofNat (8 * (index + 1))).toUInt32).toNat + 8 ≤
          ((source + UInt64.ofNat (8 * (readIndex + 1))).toUInt32).toNat
      rw [hInput.elementAddress_toNat readIndex hr, hWrite]
      omega

#print axioms writeWord_array
#print axioms writeWord_preserves_array
#print axioms writeWord_bytes_outside
end Project.EulerGridStep.Execution
