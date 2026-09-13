import Project.EulerRiemann.OutputMapOwned
import Project.EulerRiemann.ArrayAllocationExecute
import Project.ProofKit.FixedArraySearchProjection

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

def outputMapAllocationReady (params saved tail : List Wasm.Value)
    (need previous current capacity next root : UInt64)
    (hStart : params.length + saved.length = 42) : Locals :=
  outputMapReadyFrame (FixedArraySearch.frame params saved tail need previous current capacity next root)
    root (by simp only [Locals.validIndex, FixedArraySearch.frame,
      List.length_append, List.length_cons, List.length_nil]; omega)

theorem output_map_allocate_spec (pressure : Bool) (env : HostEnv Unit)
    (store : Store Unit) (heap : Heap) (params saved tail : List Wasm.Value)
    (hParams : params.length = 5) (hSaved : saved.length = 37) (hTail : tail.length = 9)
    (hStart : params.length + saved.length = 42)
    (need previous current capacity next result : UInt64)
    (source : FreeNode) (grid : Array Traversal.Cell)
    (hHeap : heap.At store) (hOwner : heap.Owns store source grid)
    (hNeed : 8 * (grid.size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536)
    (hSource : ({ params := params, locals := saved, values := [] } : Locals).get 36 =
      some (.i64 source.root))
    (hCount : ({ params := params, locals := saved, values := [] } : Locals).get 37 =
      some (.i64 (UInt64.ofNat grid.size)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next final resultFrame,
      (heap.allocate need).At final →
      (heap.allocate need).Owns final source grid →
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes)
        (outputMapResult pressure grid) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore store need 1) final
        (allocatedRoot heap.top need heap.nodes).toNat
        ((allocatedRoot heap.top need heap.nodes).toNat + 8 * (grid.size + 1)) →
      OutputMapFrameAt pressure (outputMapAllocationReady params saved tail need previous current
        capacity next (allocatedRoot heap.top need heap.nodes) hStart) grid.size resultFrame →
      wp module rest Q final resultFrame env) :
    wp module (FixedArrayAllocate.program 42 1 ++ outputMapDataProgram pressure ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  rw [List.append_assoc]
  apply heap_array_allocation_program_spec env store heap params saved tail 42 hStart
    need 1 previous current capacity next result hHeap
    (fun hNone => ⟨(hBump hNone).1.le, (hBump hNone).2⟩) hPages
  intro previousAfter currentAfter capacityAfter nextAfter
  let frame := FixedArraySearch.frame params saved tail need previousAfter currentAfter capacityAfter
    nextAfter (allocatedRoot heap.top need heap.nodes)
  have hFrameParams : frame.params.length = 5 := hParams
  have hFrameLocals : frame.locals.length = 52 := by
    simp only [frame, FixedArraySearch.frame, List.length_append, List.length_cons,
      List.length_nil, hSaved, hTail]
  have hCounter : frame.validIndex 39 := by
    simp [Locals.validIndex, hFrameParams, hFrameLocals]
  have hTarget : frame.get 47 = some (.i64 (allocatedRoot heap.top need heap.nodes)) := by
    have hGet := FixedArraySearch.frame_get params saved tail need previousAfter currentAfter
      capacityAfter nextAfter (allocatedRoot heap.top need heap.nodes) 5 (by decide)
    simpa only [hStart, Nat.reduceAdd, List.getElem?_cons_zero, List.getElem?_cons_succ] using hGet
  apply output_map_owned_spec pressure env store heap frame source need grid hHeap hOwner hNeed
    (fun hNone => (hBump hNone).1) hFrameParams hFrameLocals rfl hCounter
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 36 (by omega)).trans hSource
  · exact (FixedArraySearch.frame_get_before _ _ _ _ _ _ _ _ _ 37 (by omega)).trans hCount
  · exact hTarget
  · intro final resultFrame hFinalHeap hSourceOwner hResultOwner hWrites hFrame
    exact hNext previousAfter currentAfter capacityAfter nextAfter final resultFrame
      hFinalHeap hSourceOwner hResultOwner hWrites hFrame

#print axioms output_map_allocate_spec

end Project.EulerRiemann.Execution
