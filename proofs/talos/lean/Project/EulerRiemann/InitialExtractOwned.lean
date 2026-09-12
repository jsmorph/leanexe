import Project.EulerRiemann.InitialExtractData
import Project.EulerRiemann.HeapGridFinish
import Project.EulerRiemann.HeapGridBounds

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime FixedArrayFold FixedArrayCopy

theorem initial_extract_owned_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (source : FreeNode) (need : UInt64) (grid : Array Traversal.Cell) (size : Nat)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid) (hSize : size ≤ grid.size)
    (hNeed : 8 * (7 * size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = [])
    (hCounter : (resultFrame frame 56 (allocatedRoot heap.top need heap.nodes)).validIndex 57)
    (hSource : frame.get 48 = some (.i64 source.root))
    (hTarget : frame.get 65 = some (.i64 (allocatedRoot heap.top need heap.nodes)))
    (hLength : frame.get 53 = some (.i64 (UInt64.ofNat size)))
    (hOffset : frame.get 54 = some (.i64 0))
    (hCount : frame.get 55 = some (.i64 (UInt64.ofNat (7 * size))))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      (heap.allocate need).At final →
      (heap.allocate need).Owns final source grid →
      (heap.allocate need).Owns final (allocatedNode heap.top need heap.nodes) (grid.extract 0 size) →
      Memory.WritesGrid (heap.allocateStore initial need) final (allocatedRoot heap.top need heap.nodes) size →
      wp module rest Q final
        (counterFrame (resultFrame frame 56 (allocatedRoot heap.top need heap.nodes)) 57 (7 * size) hCounter) env) :
    wp module (initialExtractDataProgram ++ rest) Q (heap.allocateStore initial need) frame env := by
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun hNone => Nat.le_of_lt (hBump hNone)
  have hBounds := heap.allocate_grid_bounds initial need size hHeap hNeed hFit
  apply initial_extract_data_spec env _ frame source.root (allocatedRoot heap.top need heap.nodes) grid size
    hParams hLocals hValues hCounter hSource hTarget hLength hOffset hCount
    (hOwner.allocated need hHeap hFit).buffer.values hSize hBounds.1 hBounds.2
    (hOwner.allocate_grid_disjoint need size hNeed hFit) Q rest
  intro final hWrites _ hResult
  have hOutSize : (grid.extract 0 size).size = size := by
    simp only [Array.size_extract, Nat.min_eq_left hSize, Nat.sub_zero]
  have hFinished := heap.finishGrid initial final need (grid.extract 0 size) hHeap
    (by simpa only [hOutSize] using hNeed) hBump (by simpa only [hOutSize] using hWrites) hResult
  exact hNext final hFinished.1 (hOwner.swept need size hHeap hNeed hFit hWrites) hFinished.2 hWrites

#print axioms initial_extract_owned_spec

end Project.EulerRiemann.Execution
