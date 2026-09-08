import Project.EulerGridStep.ReleaseMemory

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

theorem freeHeader_of_byte_frame (initial final : Store Unit) (root capacity next : UInt64)
    (hHeader : FreeHeader initial root capacity next)
    (hBytes : ∀ address, root.toNat - 48 ≤ address → address < root.toNat →
      final.mem.bytes address = initial.mem.bytes address) :
    FreeHeader final root capacity next := by
  have hRead (offset : UInt64) (ho : 8 ≤ offset.toNat ∧ offset.toNat ≤ 48) :
      final.mem.read64 (root - offset).toUInt32 = initial.mem.read64 (root - offset).toUInt32 := by
    apply Memory.read64_congr
    intro byte hb
    apply hBytes <;>
      rw [headerAddress_toNat root offset hHeader.root48 hHeader.root32 ho.2] <;>
      have := hHeader.root48 <;> omega
  exact ⟨hHeader.root48, hHeader.root32,
    (hRead 40 (by decide)).trans hHeader.refcount,
    (hRead 32 (by decide)).trans hHeader.capacityRead,
    (hRead 8 (by decide)).trans hHeader.nextRead⟩

/-- Cloning into one block preserves the rest of a separate free-list chain. -/
theorem FieldResult.preserves_free_header {choice : FieldAllocation} {initial final : Store Unit}
    {source : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    (hResult : FieldResult choice initial final source input index value)
    (other capacity next : UInt64) (otherCount : Nat)
    (hHeader : FreeHeader initial other capacity next)
    (hSeparate : ObjectsSeparate choice.root input.size other otherCount) :
    FreeHeader final other capacity next := by
  apply freeHeader_of_byte_frame initial final other capacity next hHeader
  intro address hLo hHi
  apply hResult.outside
  unfold ObjectsSeparate at hSeparate
  omega

/-- Returning a block to the free list preserves every separate existing free node. -/
theorem ReleaseResult.preserves_free_header {initial final : Store Unit} {root capacity next : UInt64}
    {input : Array UInt64} (hResult : ReleaseResult initial final root capacity next input)
    (other otherCapacity otherNext : UInt64) (otherCount : Nat)
    (hHeader : FreeHeader initial other otherCapacity otherNext)
    (hSeparate : ObjectsSeparate root input.size other otherCount) :
    FreeHeader final other otherCapacity otherNext := by
  apply freeHeader_of_byte_frame initial final other otherCapacity otherNext hHeader
  intro address hLo hHi
  apply hResult.outside
  unfold ObjectsSeparate at hSeparate
  omega

#print axioms freeHeader_of_byte_frame
#print axioms FieldResult.preserves_free_header
#print axioms ReleaseResult.preserves_free_header
end Project.EulerGridStep.Execution
