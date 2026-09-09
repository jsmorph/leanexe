import Project.EulerGridStep.InitialCapacity
import Project.EulerGridStep.InitialAllocationBump
import Project.EulerGridStep.InitialMemory

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def initialOutputFrame (frame : Locals) (heap : UInt64) (count : Nat) : Locals :=
  let allocated := initialFreshAllocFrame (initialCapacityFrame frame (UInt64.ofNat count)) heap (fieldRequest count)
  { allocated with
    locals := allocated.locals.set 33 (.i64 (UInt64.ofNat count))
    values := [] }

theorem initial_output_shape : (gridValidBody.drop 36).take 42 =
    (gridValidBody.drop 36).take 18 ++ initialAllocationRegion ++ (gridValidBody.drop 71).take 7 := rfl

/-- Actual capacity, allocation, length store and zero loop establish the initialized output. -/
theorem initial_output_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (heap pointer allocs releases frees : UInt64) (count : Nat) (input : Array UInt64)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 43)
    (hValues : frame.values = []) (hCount : frame.locals[31]? = some (.i64 (UInt64.ofNat count)))
    (hZero : frame.locals[34]? = some (.i64 0))
    (hFit : heap.toNat + 48 + 8 * (count + 1) ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) (hMemory32 : m.memIs64 = false)
    (hHeap : initial.globals.globals[0]? = some (.i64 heap))
    (hFree : initial.globals.globals[1]? = some (.i64 0))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees))
    (hInput : UInt64Array.At initial pointer input)
    (hSeparate : ObjectsSeparate (heap + 48) count pointer input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      BufferState final count [⟨heap + 48, Array.replicate count 0⟩] [] (allocs + 1) releases frees →
      final.globals.globals[0]? = some (.i64 (heap + 48 + fieldRequest count)) →
      final.mem.pages = initial.mem.pages → UInt64Array.At final pointer input →
      wp m rest Q final (initialOutputFrame frame heap count) env) :
    wp m ((gridValidBody.drop 36).take 42 ++ rest) Q initial frame env := by
  have hFit32 : heap.toNat + 48 + 8 * (count + 1) ≤ 4294967296 := by omega
  have hCount32 : 8 * (count + 1) ≤ 4294967296 := by omega
  have hRequestNat : (fieldRequest count).toNat = 8 * (count + 1) := by
    apply UInt64.toNat_ofNat_of_lt'
    change 8 * (count + 1) < 18446744073709551616
    omega
  have hCapacity := scalar_capacity_word count hCount32
  have hRoot := Allocation.root_toNat heap (by omega : heap.toNat + 48 ≤ 4294967296)
  have hRoot48 : 48 ≤ (heap + 48).toNat := by rw [hRoot]; omega
  have hRoot32 : (heap + 48).toNat < 4294967296 := by rw [hRoot]; omega
  have hCountGet := (List.getElem?_eq_some_iff.mp hCount).choose_spec
  have hZeroGet := (List.getElem?_eq_some_iff.mp hZero).choose_spec
  rw [initial_output_shape, List.append_assoc, List.append_assoc]
  apply initial_capacity_spec m env initial frame (UInt64.ofNat count) hParams hLocals hValues hCount
  apply initial_allocation_bump_spec m env initial (initialCapacityFrame frame (UInt64.ofNat count)) heap (fieldRequest count) allocs
    hParams (by simp [initialCapacityFrame, hLocals]) rfl
    (by simp [initialCapacityFrame, hLocals, hCapacity, fieldRequest])
    (by rw [hRequestNat]; omega) (by rw [hRequestNat]; exact hFit)
    hPages hMemory32 hHeap hFree hAllocs
  apply initial_fill_spec m env (FixedArrayAllocator.allocStore initial heap (fieldRequest count) 1 allocs)
    (initialFreshAllocFrame (initialCapacityFrame frame (UInt64.ofNat count)) heap (fieldRequest count)) (heap + 48) count
    (by simp [Locals.validIndex, initialFreshAllocFrame, initialFreshBumpFrame,
      initialCapacityFrame, hParams, hLocals]) rfl
    (by simp [Locals.get, initialFreshAllocFrame, initialFreshBumpFrame, initialCapacityFrame, hParams, hLocals])
    (by simp [Locals.get, initialFreshAllocFrame, initialFreshBumpFrame, initialCapacityFrame,
      hParams, hLocals, hCountGet])
    (by simp [Locals.get, initialFreshAllocFrame, initialFreshBumpFrame, initialCapacityFrame,
      hParams, hLocals, hZeroGet])
    (by rw [hRoot]; exact hFit32)
    (by simpa [FixedArrayAllocator.allocStore, FixedArrayAllocator.headerMem, Mem.write64_pages, hRoot] using hFit)
  intro final hFill
  rcases initial_buffer_state initial final heap allocs releases frees count hFit hPages hFree hAllocs
    hReleases hFrees hFill with ⟨hState, hFinalHeap, hFinalPages⟩
  have hAllocatedInput : UInt64Array.At (FixedArrayAllocator.allocStore initial heap (fieldRequest count) 1 allocs)
      pointer input := by
    have h := writeAllocationHeader_preserves_array initial pointer (heap + 48) (fieldRequest count)
      input hInput hRoot48 hRoot32 (by unfold ObjectsSeparate at hSeparate; omega)
    simpa only [UInt64Array.At, fresh_alloc_memory initial heap (fieldRequest count) allocs (by omega)] using h
  have hFinalInput := hFill.preserves_array pointer input hAllocatedInput hSeparate
  simpa [initialOutputFrame, counterFrame, Locals.set, initialFreshAllocFrame,
    initialFreshBumpFrame, initialCapacityFrame, hParams] using
    hNext final hState hFinalHeap hFinalPages hFinalInput

#print axioms initial_output_shape
#print axioms initial_output_spec
end Project.EulerGridStep.Execution
