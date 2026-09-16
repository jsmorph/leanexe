import Project.EulerCertificate.OutputAppendOwned
import Project.EulerCertificate.ArrayAllocation
import Project.ProofKit.FixedArraySearchProjection

namespace Project.EulerCertificate.Execution
open Project.EulerRiemann Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit FixedArrayFold FixedArrayCopy

def outputAppendAllocationResult (params saved tail : List Wasm.Value)
    (need previous current capacity next root : UInt64) (count : Nat)
    (hStart : params.length + saved.length = 59) : Locals :=
  counterFrame (resultFrame (FixedArraySearch.frame params saved tail need previous current capacity next root)
    55 root) 56 count
    (by simp only [Locals.validIndex, resultFrame_params, resultFrame_locals_length,
      FixedArraySearch.frame, List.length_append, List.length_cons, List.length_nil]; omega)

theorem output_append_allocate_spec (env : HostEnv Unit)
    (store : Store Unit) (heap : Heap) (params saved tail : List Wasm.Value)
    (hParams : params.length = 17) (hSaved : saved.length = 42) (hTail : tail.length = 0)
    (hStart : params.length + saved.length = 59)
    (need previous current capacity next result : UInt64)
    (source upper : FreeNode) (left right : Array UInt64)
    (hHeap : heap.At store) (hLeft : heap.OwnsWords store source left)
    (hRight : heap.OwnsWords store upper right)
    (hNeed : 8 * (left.size + right.size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536)
    (hSource : ({ params := params, locals := saved, values := [] } : Locals).get 48 =
      some (.i64 source.root))
    (hUpper : ({ params := params, locals := saved, values := [] } : Locals).get 49 =
      some (.i64 upper.root))
    (hTotalCount : ({ params := params, locals := saved, values := [] } : Locals).get 52 =
      some (.i64 (UInt64.ofNat (left.size + right.size))))
    (hLeftCount : ({ params := params, locals := saved, values := [] } : Locals).get 53 =
      some (.i64 (UInt64.ofNat left.size)))
    (hRightCount : ({ params := params, locals := saved, values := [] } : Locals).get 54 =
      some (.i64 (UInt64.ofNat right.size)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next final,
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final source left →
      (heap.allocate need).OwnsWords final upper right →
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes) (left ++ right) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore store need 1) final
        (allocatedRoot heap.top need heap.nodes).toNat
        ((allocatedRoot heap.top need heap.nodes).toNat + 8 * (left.size + right.size + 1)) →
      wp module rest Q final (outputAppendAllocationResult params saved tail need previous current
        capacity next (allocatedRoot heap.top need heap.nodes) right.size hStart) env) :
    wp module (FixedArrayAllocate.program 59 1 ++ outputAppendDataProgram ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  rw [List.append_assoc]
  apply heap_array_allocation_program_spec env store heap params saved tail 59 hStart
    need 1 previous current capacity next result hHeap
    (fun hNone => ⟨(hBump hNone).1.le, (hBump hNone).2⟩) hPages
  intro previousAfter currentAfter capacityAfter nextAfter
  let frame := FixedArraySearch.frame params saved tail need previousAfter currentAfter capacityAfter
    nextAfter (allocatedRoot heap.top need heap.nodes)
  have hFrameParams : frame.params.length = 17 := hParams
  have hFrameLocals : frame.locals.length = 48 := by
    simp only [frame, FixedArraySearch.frame, List.length_append, List.length_cons,
      List.length_nil, hSaved, hTail]
  have hCounter : frame.validIndex 56 := by simp [Locals.validIndex, hFrameParams, hFrameLocals]
  have hTarget : frame.get 64 = some (.i64 (allocatedRoot heap.top need heap.nodes)) := by
    have hGet := FixedArraySearch.frame_get params saved tail need previousAfter currentAfter
      capacityAfter nextAfter (allocatedRoot heap.top need heap.nodes) 5 (by decide)
    simpa only [hStart, Nat.reduceAdd, List.getElem?_cons_zero, List.getElem?_cons_succ] using hGet
  apply output_append_owned_spec env store heap frame source upper need left right
    hHeap hLeft hRight hNeed (fun hNone => (hBump hNone).1) hFrameParams hFrameLocals hCounter rfl
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 48 (by omega)).trans hSource
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 49 (by omega)).trans hUpper
  · exact hTarget
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 52 (by omega)).trans hTotalCount
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 53 (by omega)).trans hLeftCount
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 54 (by omega)).trans hRightCount
  · intro final hFinalHeap hLeftOwner hRightOwner hResultOwner hWrites
    exact hNext previousAfter currentAfter capacityAfter nextAfter final
      hFinalHeap hLeftOwner hRightOwner hResultOwner hWrites

#print axioms output_append_allocate_spec

end Project.EulerCertificate.Execution
