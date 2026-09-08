import Project.EulerGridStep.FieldExecution

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Full array-object separation includes each object's 48-byte runtime header. -/
def ObjectsSeparate (left : UInt64) (leftCount : Nat) (right : UInt64) (rightCount : Nat) : Prop :=
  left.toNat + 8 * (leftCount + 1) ≤ right.toNat - 48 ∨
    right.toNat + 8 * (rightCount + 1) ≤ left.toNat - 48

theorem objectsSeparate_symm {left right : UInt64} {leftCount rightCount : Nat}
    (h : ObjectsSeparate left leftCount right rightCount) :
    ObjectsSeparate right rightCount left leftCount := h.symm

theorem ownedHeader_of_byte_frame (initial final : Store Unit) (root capacity : UInt64)
    (hHeader : OwnedHeader initial root capacity)
    (hBytes : ∀ address, root.toNat - 48 ≤ address → address < root.toNat →
      final.mem.bytes address = initial.mem.bytes address) :
    OwnedHeader final root capacity := by
  have hRead (offset : UInt64) (ho : 8 ≤ offset.toNat ∧ offset.toNat ≤ 48) :
      final.mem.read64 (root - offset).toUInt32 = initial.mem.read64 (root - offset).toUInt32 := by
    apply Memory.read64_congr
    intro byte hb
    apply hBytes <;>
      rw [headerAddress_toNat root offset hHeader.root48 hHeader.root32 ho.2] <;>
      have := hHeader.root48 <;> omega
  exact ⟨hHeader.root48, hHeader.root32,
    (hRead 48 (by decide)).trans hHeader.magic,
    (hRead 40 (by decide)).trans hHeader.refcount,
    (hRead 32 (by decide)).trans hHeader.capacityRead,
    (hRead 24 (by decide)).trans hHeader.kind,
    (hRead 16 (by decide)).trans hHeader.stride,
    (hRead 8 (by decide)).trans hHeader.mask⟩

/-- A field clone preserves every separately allocated live object's metadata. -/
theorem FieldResult.preserves_header {choice : FieldAllocation} {initial final : Store Unit}
    {source : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    (hResult : FieldResult choice initial final source input index value)
    (other capacity : UInt64) (otherCount : Nat)
    (hHeader : OwnedHeader initial other capacity)
    (hSeparate : ObjectsSeparate choice.root input.size other otherCount) :
    OwnedHeader final other capacity := by
  apply ownedHeader_of_byte_frame initial final other capacity hHeader
  intro address hLo hHi
  apply hResult.outside
  unfold ObjectsSeparate at hSeparate
  omega

/-- A field clone preserves every separately allocated live object's payload. -/
theorem FieldResult.preserves_array {choice : FieldAllocation} {initial final : Store Unit}
    {source : UInt64} {input : Array UInt64} {index : Nat} {value : UInt64}
    (hResult : FieldResult choice initial final source input index value)
    (other : UInt64) (contents : Array UInt64)
    (hArray : UInt64Array.At initial other contents)
    (hSeparate : ObjectsSeparate choice.root input.size other contents.size) :
    UInt64Array.At final other contents := by
  apply arrayAt_of_byte_frame initial final other contents hArray (by rw [hResult.pages])
  intro address hLo hHi
  apply hResult.outside
  unfold ObjectsSeparate at hSeparate
  omega

#print axioms ownedHeader_of_byte_frame
#print axioms FieldResult.preserves_header
#print axioms FieldResult.preserves_array
end Project.EulerGridStep.Execution
