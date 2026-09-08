import Project.EulerGridStep.FreshRejectedFrame

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy

/-- Complete in-bounds rejected clone with an empty free list and a fresh destination. -/
theorem rejected_fresh_clone_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (unused source heapTop allocs : UInt64) (input : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hInput : UInt64Array.At initial source input) (hNonempty : 0 < input.size)
    (hValid : (FieldAllocation.fresh heapTop allocs).Valid initial source input)
    (hPages : initial.mem.pages ≤ 65536) (hMemory32 : m.memIs64 = false)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      FieldWriteState (FixedArrayAllocator.allocStore initial heapTop (fieldRequest input.size) 1 allocs)
        source (heapTop + 48) input 0 1 final →
      wp m rest Q final (rejectedFreshReturnedFrame unused source heapTop input.size index cell) env) :
    wp m (rejectedCloneBody ++ rest) Q initial
      { rejectedPrefixFrame (writerEntryFrame unused source index cell) source input.size with values := [] } env := by
  have hSize : 8 * (input.size + 1) ≤ 4294967296 := by have := hInput.1; omega
  have hRequestNat : (fieldRequest input.size).toNat = 8 * (input.size + 1) :=
    UInt64.toNat_ofNat_of_lt' (by change 8 * (input.size + 1) < 18446744073709551616; omega)
  have hReady := rejected_ready_shape unused source input.size index cell hSize
  have hFrame := rejected_fresh_allocated_frame unused source heapTop input.size index cell
  have hRegion := field_allocation_region (.fresh heapTop allocs) initial source input hInput hValid
  rcases hValid.available with ⟨hRoot, hHeap, hFree, hAllocs⟩
  have hFit := hValid.fitMemory
  change (heapTop + 48).toNat + (fieldRequest input.size).toNat ≤ _ at hFit
  rw [Allocation.root_toNat heapTop hRoot] at hFit
  rw [rejected_clone_shape]
  simp only [List.append_assoc]
  apply rejected_capacity_spec m env initial
    { rejectedPrefixFrame (writerEntryFrame unused source index cell) source input.size with values := [] }
    (UInt64.ofNat input.size)
    (by simp [rejectedPrefixFrame, writerEntryFrame, writerParameters])
    (by simp [rejectedPrefixFrame, writerEntryFrame]) rfl
    (by simp [rejectedPrefixFrame, writerEntryFrame]) Q _
  change wp m (rejectedAllocationRegion ++ (rejectedCloneBody.drop 39 ++ rest)) Q initial
    (rejectedReadyFrame unused source input.size index cell) env
  apply rejected_allocation_bump_spec m env initial _ heapTop (fieldRequest input.size) allocs
    hReady.1 hReady.2.1 hReady.2.2.1 hReady.2.2.2 (by rw [hRequestNat]; omega)
    hFit hPages hMemory32 hHeap hFree hAllocs Q _
  rw [rejected_copy_update_shape]
  apply copy_update_spec 67 m env
    (FixedArrayAllocator.allocStore initial heapTop (fieldRequest input.size) 1 allocs) _
    source (heapTop + 48) input 0 1 hFrame.counter hFrame.values hFrame.sourceGet hFrame.targetGet
    hFrame.indexGet hFrame.lengthGet hFrame.countGet hFrame.valueGet
    hRegion.inputAt hNonempty hRegion.fit32 hRegion.fitMemory
    (by have := hValid.separate
        change source.toNat + 8 * (input.size + 1) ≤ (heapTop + 48).toNat - 48 ∨
          (heapTop + 48).toNat + 8 * (input.size + 1) ≤ source.toNat at this
        omega) Q rest
  exact hNext

#print axioms rejected_fresh_clone_spec
end Project.EulerGridStep.Execution
