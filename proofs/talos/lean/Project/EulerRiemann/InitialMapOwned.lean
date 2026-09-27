import Project.EulerRiemann.InitialMapData
import Project.EulerRiemann.HeapGridFinish
import Project.EulerRiemann.HeapGridBounds

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

theorem initial_map_owned_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (n offset : Nat) (source : FreeNode) (need : UInt64)
    (grid : Array Traversal.Cell)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hNeed : 8 * (7 * grid.size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hCounter : frame.validIndex 51)
    (hn : n ≤ 800)
    (hSum : ∀ i : Nat, (h : i < grid.size) → grid[i].index + offset < 1048576)
    (hN : frame.get 1 = some (.i64 (UInt64.ofNat n)))
    (hOffset : frame.get 10 = some (.i64 (UInt64.ofNat offset)))
    (hSource : frame.get 48 = some (.i64 source.root))
    (hCount : frame.get 49 = some (.i64 (UInt64.ofNat grid.size)))
    (hTarget : frame.get 59 = some (.i64 (allocatedRoot heap.top need heap.nodes)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      (heap.allocate need).At final →
      (heap.allocate need).Owns final source grid →
      (heap.allocate need).Owns final (allocatedNode heap.top need heap.nodes)
        (initialMapOutput n offset grid) →
      Memory.WritesGrid (heap.allocateStore initial need) final
        (allocatedRoot heap.top need heap.nodes) grid.size →
      InitialMapFrameAt
        (initialMapReadyFrame frame (allocatedRoot heap.top need heap.nodes) hCounter)
        grid.size resultFrame →
      wp module rest Q final resultFrame env) :
    wp module (initialMapDataProgram ++ rest) Q (heap.allocateStore initial need) frame env := by
  let target := allocatedRoot heap.top need heap.nodes
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun hNone => Nat.le_of_lt (hBump hNone)
  have hAllocatedOwner := hOwner.allocated need hHeap hFit
  have hBounds := heap.allocate_grid_bounds initial need grid.size hHeap hNeed hFit
  apply initial_map_data_spec env _ frame n offset source.root target grid hParams hLocals
    hValues hCounter hn hSum hN hOffset hSource hCount hTarget hAllocatedOwner.buffer.values
    hBounds.1 hBounds.2 (hOwner.allocate_grid_disjoint need grid.size hNeed hFit) Q rest
  intro final resultFrame _ hGrid hWrites hFrame
  have hOutSize : (initialMapOutput n offset grid).size = grid.size := by
    simp only [initialMapOutput, Array.size_map]
  have hFinished := heap.finishGrid initial final need (initialMapOutput n offset grid) hHeap
    (by simpa only [hOutSize] using hNeed) hBump (by simpa only [hOutSize] using hWrites) hGrid
  exact hNext final resultFrame hFinished.1
    (hOwner.swept need grid.size hHeap hNeed hFit hWrites) hFinished.2 hWrites hFrame

#print axioms initial_map_owned_spec

end Project.EulerRiemann.Execution
