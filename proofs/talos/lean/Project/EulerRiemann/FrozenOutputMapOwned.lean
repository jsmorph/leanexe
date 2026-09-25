import Project.EulerRiemann.FrozenOutputMapData
import Project.EulerRiemann.FrozenHeapWordsFinish

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit

theorem output_map_owned_spec (pressure : Bool) (env : HostEnv Unit)
    (initial : Store Unit) (heap : Heap) (frame : Locals)
    (source : FreeNode) (need : UInt64) (grid : Array Traversal.Cell)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial source grid)
    (hNeed : 8 * (grid.size + 1) ≤ need.toNat)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hCounter : frame.validIndex 39)
    (hSource : frame.get 36 = some (.i64 source.root))
    (hCount : frame.get 37 = some (.i64 (UInt64.ofNat grid.size)))
    (hTarget : frame.get 47 = some (.i64 (allocatedRoot heap.top need heap.nodes)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      (heap.allocate need).At final →
      (heap.allocate need).Owns final source grid →
      (heap.allocate need).OwnsWords final (allocatedNode heap.top need heap.nodes)
        (outputMapResult pressure grid) →
      ProofKit.Memory.WritesRange (heap.allocateArrayStore initial need 1) final
        (allocatedRoot heap.top need heap.nodes).toNat
        ((allocatedRoot heap.top need heap.nodes).toNat + 8 * (grid.size + 1)) →
      OutputMapFrameAt pressure
        (outputMapReadyFrame frame (allocatedRoot heap.top need heap.nodes) hCounter)
        grid.size resultFrame →
      wp module rest Q final resultFrame env) :
    wp module (outputMapDataProgram pressure ++ rest) Q
      (heap.allocateArrayStore initial need 1) frame env := by
  let target := allocatedRoot heap.top need heap.nodes
  have hFit : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun hNone => (hBump hNone).le
  have hAllocatedOwner := hOwner.arrayAllocated need 1 hHeap hFit
  have hBounds := allocated_bounds initial heap.top need heap.nodes hHeap.freeList hFit
  change 48 ≤ target.toNat ∧
    target.toNat + (allocatedCapacity need heap.nodes).toNat ≤ 4294967296 ∧
    target.toNat + (allocatedCapacity need heap.nodes).toNat ≤
      (allocatedStore initial heap.top need heap.nodes).mem.pages * 65536 at hBounds
  have hCapacity := allocated_capacity need heap.nodes
  have hTarget32 : target.toNat + 8 * (grid.size + 1) ≤ 4294967296 := by omega
  have hTargetFit : target.toNat + 8 * (grid.size + 1) ≤
      (heap.allocateArrayStore initial need 1).mem.pages * 65536 := by
    change target.toNat + 8 * (grid.size + 1) ≤
      (FixedArrayAllocate.allocated initial heap.top need 1 heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    omega
  have hSep := allocated_region_disjoint heap.top need source heap.nodes hOwner.buffer.rootBound
    hOwner.separated hOwner.below hFit
  have hSourceCapacity := hOwner.buffer.capacity
  have hSourceRoot := hOwner.buffer.rootBound
  change regionsDisjoint source.region
    ({ root := target, capacity := allocatedCapacity need heap.nodes } : FreeNode).region at hSep
  simp only [regionsDisjoint, FreeNode.region] at hSep
  apply output_map_data_spec pressure env _ frame source.root target grid
    hParams hLocals hValues hCounter hSource hCount hTarget hAllocatedOwner.buffer.values
    hTarget32 hTargetFit (by omega) Q rest
  intro final resultFrame _ hWords hWrites hFrame
  have hOutSize : (outputMapResult pressure grid).size = grid.size := Array.size_map ..
  have hFinished := heap.finishWords initial final need (outputMapResult pressure grid) hHeap
    (by simpa only [hOutSize] using hNeed) hBump (by simpa only [hOutSize] using hWrites) hWords
  exact hNext final resultFrame hFinished.1 (hAllocatedOwner.writesRange hWrites (by omega))
    hFinished.2 hWrites hFrame

#print axioms output_map_owned_spec

end Project.EulerRiemann.Frozen.Execution
