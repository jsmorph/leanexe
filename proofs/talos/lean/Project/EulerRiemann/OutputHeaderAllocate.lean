import Project.EulerRiemann.OutputHeaderData
import Project.EulerRiemann.ArrayAllocationExecute
import Project.ProofKit.FixedArraySearchProjection

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

theorem output_header_allocate_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved : List Wasm.Value) (hParams : params.length = 5) (hSaved : saved.length = 46)
    (hStart : params.length + saved.length = 51)
    (need previous current capacity next result n time status : UInt64)
    (hHeap : heap.At store) (hNeed : 40 ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536)
    (hN : ({ params := params, locals := saved, values := [] } : Locals).get 0 = some (.i64 n))
    (hTime : ({ params := params, locals := saved, values := [] } : Locals).get 1 = some (.i64 time))
    (hStatus : ({ params := params, locals := saved, values := [] } : Locals).get 2 = some (.i64 status))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next final,
      (heap.allocate need).At final →
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes)
        (outputHeaderWords n time status) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore store need 1) final
        (allocatedRoot heap.top need heap.nodes).toNat
        ((allocatedRoot heap.top need heap.nodes).toNat + 40) →
      wp module rest Q final (outputHeaderResultFrame
        (FixedArraySearch.frame params saved [] need previous current capacity next
          (allocatedRoot heap.top need heap.nodes))
        (allocatedRoot heap.top need heap.nodes) n) env) :
    wp module (FixedArrayAllocate.program 51 1 ++ outputHeaderDataProgram ++ rest) Q store
      (FixedArraySearch.frame params saved [] need previous current capacity next result) env := by
  rw [List.append_assoc]
  apply heap_array_allocation_program_spec env store heap params saved [] 51 hStart
    need 1 previous current capacity next result hHeap
    (fun hNone => ⟨(hBump hNone).1.le, (hBump hNone).2⟩) hPages
  intro previousAfter currentAfter capacityAfter nextAfter
  let frame := FixedArraySearch.frame params saved [] need previousAfter currentAfter capacityAfter
    nextAfter (allocatedRoot heap.top need heap.nodes)
  have hFrameLocals : frame.locals.length = 52 := by
    simp only [frame, FixedArraySearch.frame, List.length_append, List.length_cons,
      List.length_nil, hSaved]
  have hRoot : frame.get 56 = some (.i64 (allocatedRoot heap.top need heap.nodes)) := by
    have hGet := FixedArraySearch.frame_get params saved [] need previousAfter currentAfter
      capacityAfter nextAfter (allocatedRoot heap.top need heap.nodes) 5 (by decide)
    simpa only [hStart, Nat.reduceAdd, List.getElem?_cons_zero, List.getElem?_cons_succ] using hGet
  apply output_header_owned_spec env store heap frame need n time status hHeap hNeed
    (fun hNone => (hBump hNone).1) hParams hFrameLocals rfl
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 0 (by omega)).trans hN
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 1 (by omega)).trans hTime
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 2 (by omega)).trans hStatus
  · exact hRoot
  · intro final hFinalHeap hOwner hWrites
    exact hNext previousAfter currentAfter capacityAfter nextAfter final hFinalHeap hOwner hWrites

#print axioms output_header_allocate_spec

end Project.EulerRiemann.Execution
