import Project.EulerGridStep.RejectedReuseSearch
import Project.EulerGridStep.RejectedAllocationShape
import Project.EulerGridStep.FieldAllocationReuse

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def rejectedReuseAllocFrame (base : Locals) (root capacity next : UInt64) : Locals :=
  { rejectedReuseFoundFrame base root capacity next with
    locals := (rejectedReuseFoundFrame base root capacity next).locals.set 61 (.i64 root) }

/-- Complete emitted allocation via a sufficient first free block, with no bump or growth. -/
theorem rejected_allocation_reuse_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (base : Locals) (root capacity request next allocs : UInt64)
    (hParams : base.params.length = 10) (hLocals : base.locals.length = 72)
    (hValues : base.values = []) (hRequest : base.locals[66]? = some (.i64 request))
    (hFreeList : initial.globals.globals[1]? = some (.i64 root))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs))
    (hRoot48 : 48 ≤ root.toNat) (hRoot32 : root.toNat < 4294967296)
    (hFit : root.toNat ≤ initial.mem.pages * 65536)
    (hCapacityRead : initial.mem.read64 (root - 32).toUInt32 = capacity)
    (hNextRead : initial.mem.read64 (root - 8).toUInt32 = next)
    (hEnough : capacity ≥ request)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hContinue : wp m rest Q (reuseAllocatedStore initial root capacity next allocs)
      (rejectedReuseAllocFrame base root capacity next) env) :
    wp m (rejectedAllocationRegion ++ rest) Q initial base env := by
  have hRoot0 : root ≠ 0 := by intro h; subst root; simp at hRoot48
  simp only [rejectedAllocationRegion, List.append_assoc, List.cons_append, List.nil_append]
  wp_alloc_window_lists [hParams, hLocals, hValues, hFreeList]
  change wp m (search 67 1 ++ _) Q initial (rejectedReuseSearchFrame base root) env
  apply rejected_reuse_search_spec m env initial base root capacity request next hParams hLocals hRequest
    hFreeList hRoot48 hRoot32 hFit hCapacityRead hNextRead hEnough Q _
  wp_alloc_window_lists [rejectedReuseFoundFrame, rejectedReuseChosenFrame, rejectedReuseLoadedFrame, rejectedReuseSearchFrame,
    hParams, hLocals, hRoot0]
  apply wp_iff_cons rfl
  rw [ite_eq_right (by simp [hRoot0])]
  rw [wp_nil]
  have hReuseAllocs : (reuseStore initial root capacity next).globals.globals[2]? = some (.i64 allocs) := by
    simp [reuseStore, writeAllocationHeader, writeHeaderWord, reuseUnlinkedStore, hAllocs]
  wp_alloc_window_lists [rejectedReuseFoundFrame, rejectedReuseChosenFrame, rejectedReuseLoadedFrame, rejectedReuseSearchFrame,
    hParams, hLocals, hReuseAllocs]
  simpa only [reuseAllocatedStore, rejectedReuseAllocFrame, rejectedReuseFoundFrame, rejectedReuseChosenFrame,
    rejectedReuseLoadedFrame, rejectedReuseSearchFrame] using hContinue

#print axioms rejected_allocation_reuse_spec
end Project.EulerGridStep.Execution
