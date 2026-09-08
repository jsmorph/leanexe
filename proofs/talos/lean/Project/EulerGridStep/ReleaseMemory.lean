import Project.EulerGridStep.ObjectFrame

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The exact two metadata writes when releasing an owned scalar array. -/
def releasedMemory (initial : Store Unit) (root next : UInt64) : Mem :=
  (initial.mem.write64 (root - 40).toUInt32 0).write64 (root - 8).toUInt32 next

structure FreeHeader (current : Store Unit) (root capacity next : UInt64) : Prop where
  root48 : 48 ≤ root.toNat
  root32 : root.toNat < 4294967296
  refcount : current.mem.read64 (root - 40).toUInt32 = 0
  capacityRead : current.mem.read64 (root - 32).toUInt32 = capacity
  nextRead : current.mem.read64 (root - 8).toUInt32 = next

structure ReleaseResult (initial final : Store Unit) (root capacity next : UInt64)
    (input : Array UInt64) : Prop where
  memory : final.mem = releasedMemory initial root next
  header : FreeHeader final root capacity next
  array : UInt64Array.At final root input
  pages : final.mem.pages = initial.mem.pages
  outside : ∀ address, address < root.toNat - 48 ∨ root.toNat ≤ address →
    final.mem.bytes address = initial.mem.bytes address

theorem releasedMemory_outside (initial : Store Unit) (root next : UInt64)
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (address : Nat) (hOutside : address < root.toNat - 48 ∨ root.toNat ≤ address) :
    (releasedMemory initial root next).bytes address = initial.mem.bytes address := by
  have h40 : (root - 40).toUInt32.toNat = root.toNat - 40 :=
    headerAddress_toNat root 40 hRoot48 hRoot32 (by decide)
  have h8 : (root - 8).toUInt32.toNat = root.toNat - 8 :=
    headerAddress_toNat root 8 hRoot48 hRoot32 (by decide)
  unfold releasedMemory
  repeat rw [Memory.write64_bytes_outside _ _ _ (by simp only [h40, h8]; omega)]

/-- Exact release memory establishes a reusable header without altering any payload byte. -/
theorem release_result_of_memory (initial final : Store Unit) (root capacity next : UInt64)
    (input : Array UInt64) (hHeader : OwnedHeader initial root capacity)
    (hArray : UInt64Array.At initial root input)
    (hMem : final.mem = releasedMemory initial root next) :
    ReleaseResult initial final root capacity next input := by
  have h40 : (root - 40).toUInt32.toNat = root.toNat - 40 :=
    headerAddress_toNat root 40 hHeader.root48 hHeader.root32 (by decide)
  have h32 : (root - 32).toUInt32.toNat = root.toNat - 32 :=
    headerAddress_toNat root 32 hHeader.root48 hHeader.root32 (by decide)
  have h8 : (root - 8).toUInt32.toNat = root.toNat - 8 :=
    headerAddress_toNat root 8 hHeader.root48 hHeader.root32 (by decide)
  have hPages : final.mem.pages = initial.mem.pages := by
    rw [hMem]
    simp [releasedMemory, Mem.write64_pages]
  have hOutside : ∀ address, address < root.toNat - 48 ∨ root.toNat ≤ address →
      final.mem.bytes address = initial.mem.bytes address := by
    intro address h
    rw [hMem]
    exact releasedMemory_outside initial root next hHeader.root48 hHeader.root32 address h
  refine ⟨hMem, ⟨hHeader.root48, hHeader.root32, ?_, ?_, ?_⟩, ?_, hPages, hOutside⟩
  · rw [hMem]
    unfold releasedMemory
    rw [Memory.read64_write64_disjoint _ _ _ _ (by simp only [h40, h8]; have := hHeader.root48; omega),
      read64_write64_exact]
  · rw [hMem]
    unfold releasedMemory
    rw [Memory.read64_write64_disjoint _ _ _ _ (by simp only [h32, h8]; have := hHeader.root48; omega),
      Memory.read64_write64_disjoint _ _ _ _ (by simp only [h32, h40]; have := hHeader.root48; omega)]
    exact hHeader.capacityRead
  · rw [hMem]
    exact read64_write64_exact _ _ _
  · apply arrayAt_of_byte_frame initial final root input hArray (by rw [hPages])
    intro address hLo _
    exact hOutside address (Or.inr hLo)

theorem ReleaseResult.preserves_header {initial final : Store Unit} {root capacity next : UInt64}
    {input : Array UInt64} (hResult : ReleaseResult initial final root capacity next input)
    (other otherCapacity : UInt64) (otherCount : Nat)
    (hHeader : OwnedHeader initial other otherCapacity)
    (hSeparate : ObjectsSeparate root input.size other otherCount) :
    OwnedHeader final other otherCapacity := by
  apply ownedHeader_of_byte_frame initial final other otherCapacity hHeader
  intro address hLo hHi
  apply hResult.outside
  unfold ObjectsSeparate at hSeparate
  omega

theorem ReleaseResult.preserves_array {initial final : Store Unit} {root capacity next : UInt64}
    {input : Array UInt64} (hResult : ReleaseResult initial final root capacity next input)
    (other : UInt64) (contents : Array UInt64)
    (hArray : UInt64Array.At initial other contents)
    (hSeparate : ObjectsSeparate root input.size other contents.size) :
    UInt64Array.At final other contents := by
  apply arrayAt_of_byte_frame initial final other contents hArray (by rw [hResult.pages])
  intro address hLo hHi
  apply hResult.outside
  unfold ObjectsSeparate at hSeparate
  omega

#print axioms releasedMemory_outside
#print axioms release_result_of_memory
#print axioms ReleaseResult.preserves_header
#print axioms ReleaseResult.preserves_array
end Project.EulerGridStep.Execution
