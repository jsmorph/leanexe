import Project.EulerGridStep.InvalidEntryAllocation
import Project.EulerGridStep.HeaderMemory

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def invalidEntryStore (initial : Store Unit) (heap allocs : UInt64) : Store Unit :=
  let allocated := FixedArrayAllocator.allocStore initial heap 16 1 allocs
  { allocated with
    mem := (allocated.mem.write64 (heap + 48).toUInt32 1).write64 (heap + 48 + 8).toUInt32 1 }

def invalidEntryResultFrame (frame : Locals) (heap : UInt64) : Locals :=
  let allocated := invalidEntryFreshAllocFrame (FixedArrayCapacity.capacityFrame frame 37 16) heap 16
  { allocated with
    locals := ((allocated.locals.set 34 (.i64 1)).set 1 (.i64 (heap + 48))).set 30 (.i64 (heap + 48))
    values := [] }

theorem invalid_entry_shape : gridInvalidBody = FixedArrayCapacity.constantProgram 1 1 37 ++
    invalidEntryAllocationRegion ++ gridInvalidBody.drop 35 := rfl

/-- The rejected singleton is proved using the exact byte-store lemma, without native evaluation axioms. -/
theorem invalid_entry_store_at (initial : Store Unit) (heap allocs : UInt64)
    (hFit : heap.toNat + 48 + 16 ≤ initial.mem.pages * 65536) (hPages : initial.mem.pages ≤ 65536) :
    UInt64Array.At (invalidEntryStore initial heap allocs) (heap + 48) #[1] := by
  have hFacts := Allocation.bumpFacts heap 16 initial.mem.pages hFit hPages
  have hRoot : (heap + 48).toUInt32.toNat = heap.toNat + 48 := by
    simpa using hFacts.wordAddress_toNat 0 (by decide)
  have hPayload : (heap + 48 + 8).toUInt32.toNat = heap.toNat + 56 := by
    simpa using hFacts.wordAddress_toNat 1 (by decide)
  apply UInt64Array.singleton
  · rw [hFacts.rootToNat]
    exact hFacts.fit32
  · rw [hFacts.rootToNat]
    simpa [invalidEntryStore, FixedArrayAllocator.allocStore_pages, Mem.write64_pages] using hFit
  · change (((FixedArrayAllocator.allocStore initial heap 16 1 allocs).mem.write64
      (heap + 48).toUInt32 1).write64 (heap + 48 + 8).toUInt32 1).read64 (heap + 48).toUInt32 = 1
    rw [Memory.read64_write64_disjoint _ _ _ _ (Or.inl (by omega)), read64_write64_exact]
  · exact read64_write64_exact _ _ _

/-- Complete emitted invalid entry: allocate and initialize [1], staging its result pointer. -/
theorem invalid_entry_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (heap allocs : UInt64)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 43) (hValues : frame.values = [])
    (hFit : heap.toNat + 48 + 16 ≤ initial.mem.pages * 65536) (hPages : initial.mem.pages ≤ 65536)
    (hMemory32 : m.memIs64 = false)
    (hHeap : initial.globals.globals[0]? = some (.i64 heap))
    (hFree : initial.globals.globals[1]? = some (.i64 0))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : UInt64Array.At (invalidEntryStore initial heap allocs) (heap + 48) #[1] →
      wp m rest Q (invalidEntryStore initial heap allocs) (invalidEntryResultFrame frame heap) env) :
    wp m (gridInvalidBody ++ rest) Q initial frame env := by
  have hFacts := Allocation.bumpFacts heap 16 initial.mem.pages hFit hPages
  have hRootBound : (heap.toNat + 48) % 4294967296 + 8 ≤ initial.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by have := hFacts.fit32; omega)]
    omega
  have hPayloadBound : (heap.toNat + 48 + 8) % 4294967296 + 8 ≤ initial.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by have := hFacts.fit32; omega)]
    omega
  have hRootSafe := Nat.not_lt.mpr hRootBound
  have hPayloadSafe := Nat.not_lt.mpr hPayloadBound
  have hRootAddress : UInt32.ofNat ((heap.toNat + 48) % 4294967296) = (heap + 48).toUInt32 := by
    simpa using hFacts.wordAddress 0 (by decide)
  have hPayloadAddress : UInt32.ofNat ((heap.toNat + 48 + 8) % 4294967296) = (heap + 48 + 8).toUInt32 := by
    have hRoot64 : heap.toNat + 48 < 18446744073709551616 := by have := hFacts.fit32; omega
    simpa [Nat.mod_eq_of_lt hRoot64] using hFacts.wordAddress 1 (by decide)
  rw [invalid_entry_shape, List.append_assoc, List.append_assoc]
  apply FixedArrayCapacity.constantProgram_spec 1 1 37 m env initial frame hValues (by omega)
    (by simp [Locals.validIndex, hParams, hLocals])
  change wp m (invalidEntryAllocationRegion ++ (gridInvalidBody.drop 35 ++ rest)) Q initial
    (FixedArrayCapacity.capacityFrame frame 37 16) env
  apply invalid_entry_allocation_bump_spec m env initial (FixedArrayCapacity.capacityFrame frame 37 16) heap 16 allocs
    hParams (by simp [FixedArrayCapacity.capacityFrame, hLocals]) rfl
    (by simp [FixedArrayCapacity.capacityFrame, hParams, hLocals]) (by decide)
    hFit hPages hMemory32 hHeap hFree hAllocs
  wp_alloc_window_lists [gridInvalidBody, func36, invalidEntryFreshAllocFrame, invalidEntryFreshBumpFrame,
    FixedArrayCapacity.capacityFrame, hParams, hLocals, hValues,
    FixedArrayAllocator.allocStore_pages, hFacts.rootToNat, hRootBound, hPayloadBound,
    hRootAddress, hPayloadAddress, hRootSafe, hPayloadSafe]
  simpa [invalidEntryStore, invalidEntryResultFrame, invalidEntryFreshAllocFrame,
    invalidEntryFreshBumpFrame, FixedArrayCapacity.capacityFrame, hParams, hValues] using
    hNext (invalid_entry_store_at initial heap allocs hFit hPages)

#print axioms invalid_entry_shape
#print axioms invalid_entry_store_at
#print axioms invalid_entry_spec
end Project.EulerGridStep.Execution
