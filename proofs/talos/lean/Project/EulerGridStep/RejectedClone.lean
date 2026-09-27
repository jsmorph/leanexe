import Project.EulerGridStep.RejectedFrame

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy

def rejectedReturnedFrame (unused source root capacity next : UInt64) (count index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) : Locals :=
  { counterFrame
      (rejectedReuseAllocFrame (rejectedReadyFrame unused source count index cell) root capacity next)
      72 count (rejected_allocated_frame unused source root capacity next count index cell).counter with
    values := [.i64 root] }

/-- The complete in-bounds rejected clone, using the first sufficient free block. -/
theorem rejected_clone_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (unused source root capacity next allocs : UInt64) (input : Array UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell)
    (hInput : UInt64Array.At initial source input) (hNonempty : 0 < input.size)
    (hValid : (FieldAllocation.reuse root capacity next allocs).Valid initial source input)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      FieldWriteState (reuseAllocatedStore initial root capacity next allocs) source root input 0 1 final →
      wp m rest Q final (rejectedReturnedFrame unused source root capacity next input.size index cell) env) :
    wp m (rejectedCloneBody ++ rest) Q initial
      { rejectedPrefixFrame (writerEntryFrame unused source index cell) source input.size with values := [] } env := by
  have hSize : 8 * (input.size + 1) ≤ 4294967296 := by have := hInput.1; omega
  have hRequestNat : (fieldRequest input.size).toNat = 8 * (input.size + 1) :=
    UInt64.toNat_ofNat_of_lt' (by change 8 * (input.size + 1) < 18446744073709551616; omega)
  have hReady := rejected_ready_shape unused source input.size index cell hSize
  have hFrame := rejected_allocated_frame unused source root capacity next input.size index cell
  have hRegion := field_allocation_region (.reuse root capacity next allocs) initial source input hInput hValid
  rcases hValid.available with ⟨hFree, hAllocs, hCapacity, hNextRead⟩
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
  apply rejected_allocation_reuse_spec m env initial _ root capacity (fieldRequest input.size) next allocs
    hReady.1 hReady.2.1 hReady.2.2.1 hReady.2.2.2 hFree hAllocs hValid.root48 hValid.root32
    (by have := hValid.fitMemory; change root.toNat + capacity.toNat ≤ _ at this; omega)
    hCapacity hNextRead
    (by change (fieldRequest input.size).toNat ≤ capacity.toNat; rw [hRequestNat]; exact hValid.enough) Q _
  rw [rejected_copy_update_shape]
  apply copy_update_spec 67 m env (reuseAllocatedStore initial root capacity next allocs) _
    source root input 0 1 hFrame.counter hFrame.values hFrame.sourceGet hFrame.targetGet
    hFrame.indexGet hFrame.lengthGet hFrame.countGet hFrame.valueGet
    hRegion.inputAt hNonempty hRegion.fit32 hRegion.fitMemory
    (by have := hValid.separate; change source.toNat + 8 * (input.size + 1) ≤ root.toNat - 48 ∨
          root.toNat + 8 * (input.size + 1) ≤ source.toNat at this; omega) Q rest
  exact hNext

#print axioms rejected_clone_spec
end Project.EulerGridStep.Execution
