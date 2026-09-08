import Project.EulerGridStep.AllocationHeader
import Project.EulerGridStep.ArrayFrame
import Project.EulerGridStep.FieldTailModel

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Runtime metadata for one owned array of scalar words. -/
structure OwnedHeader (initial : Store Unit) (root capacity : UInt64) : Prop where
  root48 : 48 ≤ root.toNat
  root32 : root.toNat < 4294967296
  magic : initial.mem.read64 (root - 48).toUInt32 = 5501223100278326855
  refcount : initial.mem.read64 (root - 40).toUInt32 = 1
  capacityRead : initial.mem.read64 (root - 32).toUInt32 = capacity
  kind : initial.mem.read64 (root - 24).toUInt32 = 2
  stride : initial.mem.read64 (root - 16).toUInt32 = 1
  mask : initial.mem.read64 (root - 8).toUInt32 = 0

theorem headerAddress_toNat (root offset : UInt64)
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hOffset : offset.toNat ≤ 48) :
    (root - offset).toUInt32.toNat = root.toNat - offset.toNat := by
  rw [Memory.toUInt32_toNat, Memory.toNat_sub_of_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]

theorem writeAllocationHeader_owned (initial : Store Unit) (root capacity : UInt64)
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296) :
    OwnedHeader (writeAllocationHeader initial root capacity) root capacity := by
  have h48 : (root - 48).toUInt32.toNat = root.toNat - 48 :=
    headerAddress_toNat root 48 hRoot48 hRoot32 (by decide)
  have h40 : (root - 40).toUInt32.toNat = root.toNat - 40 :=
    headerAddress_toNat root 40 hRoot48 hRoot32 (by decide)
  have h32 : (root - 32).toUInt32.toNat = root.toNat - 32 :=
    headerAddress_toNat root 32 hRoot48 hRoot32 (by decide)
  have h24 : (root - 24).toUInt32.toNat = root.toNat - 24 :=
    headerAddress_toNat root 24 hRoot48 hRoot32 (by decide)
  have h16 : (root - 16).toUInt32.toNat = root.toNat - 16 :=
    headerAddress_toNat root 16 hRoot48 hRoot32 (by decide)
  have h8 : (root - 8).toUInt32.toNat = root.toNat - 8 :=
    headerAddress_toNat root 8 hRoot48 hRoot32 (by decide)
  refine ⟨hRoot48, hRoot32, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [writeAllocationHeader, writeHeaderWord] <;>
    repeat first
      | rw [read64_write64_exact]
      | rw [Memory.read64_write64_disjoint _ _ _ _ (by
          simp only [h48, h40, h32, h24, h16, h8]; omega)]

theorem writeAllocationHeader_bytes_outside (initial : Store Unit) (root capacity : UInt64)
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296) (address : Nat)
    (hOutside : address < root.toNat - 48 ∨ root.toNat ≤ address) :
    (writeAllocationHeader initial root capacity).mem.bytes address = initial.mem.bytes address := by
  have h48 : (root - 48).toUInt32.toNat = root.toNat - 48 :=
    headerAddress_toNat root 48 hRoot48 hRoot32 (by decide)
  have h40 : (root - 40).toUInt32.toNat = root.toNat - 40 :=
    headerAddress_toNat root 40 hRoot48 hRoot32 (by decide)
  have h32 : (root - 32).toUInt32.toNat = root.toNat - 32 :=
    headerAddress_toNat root 32 hRoot48 hRoot32 (by decide)
  have h24 : (root - 24).toUInt32.toNat = root.toNat - 24 :=
    headerAddress_toNat root 24 hRoot48 hRoot32 (by decide)
  have h16 : (root - 16).toUInt32.toNat = root.toNat - 16 :=
    headerAddress_toNat root 16 hRoot48 hRoot32 (by decide)
  have h8 : (root - 8).toUInt32.toNat = root.toNat - 8 :=
    headerAddress_toNat root 8 hRoot48 hRoot32 (by decide)
  simp only [writeAllocationHeader, writeHeaderWord]
  repeat rw [Memory.write64_bytes_outside _ _ _ (by
    simp only [h48, h40, h32, h24, h16, h8]; omega)]

theorem writeAllocationHeader_preserves_array (initial : Store Unit) (source root capacity : UInt64)
    (input : Array UInt64) (hInput : UInt64Array.At initial source input)
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ root.toNat - 48 ∨
      root.toNat ≤ source.toNat) :
    UInt64Array.At (writeAllocationHeader initial root capacity) source input := by
  apply arrayAt_of_byte_frame initial _ source input hInput
    (by simp [writeAllocationHeader, writeHeaderWord_pages])
  intro address hLo hHi
  apply writeAllocationHeader_bytes_outside initial root capacity hRoot48 hRoot32 address
  omega

theorem fieldWrite_preserves_header (initial final : Store Unit) (source root capacity : UInt64)
    (input : Array UInt64) (index : Nat) (value : UInt64)
    (hHeader : OwnedHeader initial root capacity)
    (hWrite : FieldWriteState initial source root input index value final) :
    OwnedHeader final root capacity := by
  have hRead (offset : UInt64) (ho : 8 ≤ offset.toNat ∧ offset.toNat ≤ 48) :
      final.mem.read64 (root - offset).toUInt32 = initial.mem.read64 (root - offset).toUInt32 := by
    apply Memory.read64_congr
    intro byte hb
    apply hWrite.outside
    left
    rw [headerAddress_toNat root offset hHeader.root48 hHeader.root32 ho.2]
    have := hHeader.root48
    omega
  exact ⟨hHeader.root48, hHeader.root32,
    (hRead 48 (by decide)).trans hHeader.magic,
    (hRead 40 (by decide)).trans hHeader.refcount,
    (hRead 32 (by decide)).trans hHeader.capacityRead,
    (hRead 24 (by decide)).trans hHeader.kind,
    (hRead 16 (by decide)).trans hHeader.stride,
    (hRead 8 (by decide)).trans hHeader.mask⟩

#print axioms writeAllocationHeader_owned
#print axioms writeAllocationHeader_bytes_outside
#print axioms writeAllocationHeader_preserves_array
#print axioms fieldWrite_preserves_header
end Project.EulerGridStep.Execution
