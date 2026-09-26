import Project.EulerRiemann.FrozenHeapGridFinish
import Project.EulerRiemann.FrozenHeapGridBounds
import Project.EulerRiemann.FrozenMemoryLength

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit.FixedArrayResult

def Heap.emptyStore (heap : Heap) (store : Store Unit) : Store Unit :=
  writeLength (heap.allocateStore store 8) (allocatedRoot heap.top 8 heap.nodes) 0

theorem Heap.empty_owned (heap : Heap) (store : Store Unit) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 8 heap.nodes = none → heap.top.toNat + 48 + 8 < 4294967296) :
    (heap.allocate 8).At (heap.emptyStore store) ∧
      (heap.allocate 8).Owns (heap.emptyStore store) (allocatedNode heap.top 8 heap.nodes) #[] ∧
      ∀ (saved : FreeNode) (grid : Array Traversal.Cell), heap.Owns store saved grid →
        (heap.allocate 8).Owns (heap.emptyStore store) saved grid ∧
        regionsDisjoint saved.region (allocatedNode heap.top 8 heap.nodes).region := by
  have hFit : takeFirstFitFrom 0 8 heap.nodes = none →
      heap.top.toNat + 48 + (8 : UInt64).toNat ≤ 4294967296 :=
    fun hNone => Nat.le_of_lt (hBump hNone)
  have hBounds := heap.allocate_grid_bounds store 8 0 hHeap (by decide) hFit
  have hWrites := Memory.writeLength_frame (heap.allocateStore store 8)
    (allocatedRoot heap.top 8 heap.nodes) 0 hBounds.1
  have hGrid : Memory.GridAt (heap.emptyStore store) (allocatedRoot heap.top 8 heap.nodes) #[] :=
    (Memory.writeLength_prefix (heap.allocateStore store 8)
      (allocatedRoot heap.top 8 heap.nodes) #[] hBounds.1 hBounds.2).complete
  have hFinished := heap.finishGrid store (heap.emptyStore store) 8 #[] hHeap (by decide) hBump
    hWrites hGrid
  refine ⟨hFinished.1, hFinished.2, ?_⟩
  intro saved grid hOwner
  exact ⟨hOwner.swept 8 0 hHeap (by decide) hFit hWrites,
    allocated_region_disjoint heap.top 8 saved heap.nodes hOwner.buffer.rootBound
      hOwner.separated hOwner.below hFit⟩

#print axioms Heap.empty_owned

end Project.EulerRiemann.Frozen.Execution
