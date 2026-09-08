import Project.EulerGridStep.AllocationMemory
import Project.EulerGridStep.FieldAllocationReuse

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Memory conditions established by either allocation path before initializing array length. -/
structure AllocatedRegion (initial current : Store Unit) (source root capacity : UInt64)
    (input : Array UInt64) : Prop where
  inputAt : UInt64Array.At current source input
  header : OwnedHeader current root capacity
  fit32 : root.toNat + 8 * (input.size + 1) ≤ 4294967296
  fitMemory : root.toNat + 8 * (input.size + 1) ≤ current.mem.pages * 65536
  pages : current.mem.pages = initial.mem.pages
  outside : ∀ address, address < root.toNat - 48 ∨ root.toNat ≤ address →
    current.mem.bytes address = initial.mem.bytes address

theorem ownedHeader_of_mem_eq (initial current : Store Unit) (root capacity : UInt64)
    (hHeader : OwnedHeader initial root capacity) (hMem : current.mem = initial.mem) :
    OwnedHeader current root capacity := by
  refine ⟨hHeader.root48, hHeader.root32, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hMem]; exact hHeader.magic
  · rw [hMem]; exact hHeader.refcount
  · rw [hMem]; exact hHeader.capacityRead
  · rw [hMem]; exact hHeader.kind
  · rw [hMem]; exact hHeader.stride
  · rw [hMem]; exact hHeader.mask

theorem allocatedRegion_of_header_write (initial current : Store Unit) (source root capacity : UInt64)
    (input : Array UInt64) (hInput : UInt64Array.At initial source input)
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hEnough : 8 * (input.size + 1) ≤ capacity.toNat)
    (hFit32 : root.toNat + capacity.toNat ≤ 4294967296)
    (hFitMemory : root.toNat + capacity.toNat ≤ initial.mem.pages * 65536)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ root.toNat - 48 ∨
      root.toNat ≤ source.toNat)
    (hMem : current.mem = (writeAllocationHeader initial root capacity).mem) :
    AllocatedRegion initial current source root capacity input := by
  have hPages : current.mem.pages = initial.mem.pages := by
    rw [hMem]
    simp [writeAllocationHeader, writeHeaderWord_pages]
  have hArray := writeAllocationHeader_preserves_array initial source root capacity input
    hInput hRoot48 hRoot32 hSeparate
  refine ⟨?_, ownedHeader_of_mem_eq _ _ _ _
    (writeAllocationHeader_owned initial root capacity hRoot48 hRoot32) hMem,
    by omega, ?_, hPages, ?_⟩
  · simpa only [UInt64Array.At, hMem] using hArray
  · rw [hPages]
    omega
  · intro address hOutside
    rw [hMem]
    exact writeAllocationHeader_bytes_outside initial root capacity hRoot48 hRoot32 address hOutside

/-- The fresh allocator's memory is exactly the same metadata initialization model. -/
theorem fresh_alloc_memory (initial : Store Unit) (base capacity allocs : UInt64)
    (hFit32 : base.toNat + 48 ≤ 4294967296) :
    (FixedArrayAllocator.allocStore initial base capacity 1 allocs).mem =
      (writeAllocationHeader initial (base + 48) capacity).mem := by
  have hOffsets := Allocation.headerOffsets base hFit32
  have hZero : (base + 48 - 48).toNat = base.toNat := by
    have h := Allocation.root_sub_toNat base 48 hFit32 (by decide)
    simpa using h
  simp only [FixedArrayAllocator.allocStore, FixedArrayAllocator.headerMem,
    writeAllocationHeader, writeHeaderWord, Memory.toUInt32_eq_ofNat, hZero,
    hOffsets.1, hOffsets.2.1, hOffsets.2.2.1, hOffsets.2.2.2.1, hOffsets.2.2.2.2]

theorem reused_alloc_memory (initial : Store Unit) (root capacity next allocs : UInt64) :
    (reuseAllocatedStore initial root capacity next allocs).mem =
      (writeAllocationHeader initial root capacity).mem := rfl

/-- Combined allocation and payload writes touch only the new object's header and used array bytes. -/
theorem field_write_bytes_outside_object (initial allocated final : Store Unit)
    (source root capacity : UInt64) (input : Array UInt64) (index : Nat) (value : UInt64)
    (hAllocated : AllocatedRegion initial allocated source root capacity input)
    (hWrite : FieldWriteState allocated source root input index value final)
    (address : Nat)
    (hOutside : address < root.toNat - 48 ∨ root.toNat + 8 * (input.size + 1) ≤ address) :
    final.mem.bytes address = initial.mem.bytes address := by
  rw [hWrite.outside address (by omega), hAllocated.outside address (by omega)]

#print axioms allocatedRegion_of_header_write
#print axioms fresh_alloc_memory
#print axioms reused_alloc_memory
#print axioms field_write_bytes_outside_object
end Project.EulerGridStep.Execution
