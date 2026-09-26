import Project.Drone.EmptyWordsMemory

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem emptyWords_owned (heap : Heap) (store : Store Unit) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 8 heap.nodes = none → heap.top.toNat + 48 + 8 < 4294967296) :
    (heap.allocate 8).At (emptyWordsStore heap store) ∧
      (heap.allocate 8).OwnsWords (emptyWordsStore heap store)
        (allocatedNode heap.top 8 heap.nodes) #[] ∧
      ∀ (saved : FreeNode) (words : Array UInt64), heap.OwnsWords store saved words →
        (heap.allocate 8).OwnsWords (emptyWordsStore heap store) saved words ∧
        regionsDisjoint saved.region (allocatedNode heap.top 8 heap.nodes).region := by
  have hFit : takeFirstFitFrom 0 8 heap.nodes = none →
      heap.top.toNat + 48 + (8 : UInt64).toNat ≤ 4294967296 := fun h => (hBump h).le
  have hCapacity := allocated_capacity (8 : UInt64) heap.nodes
  obtain ⟨hWrites, hWords⟩ := emptyWords_memory heap store hHeap hBump
  have hFinished := heap.finishWords store (emptyWordsStore heap store) 8 #[] hHeap
    (by decide) hBump (by simpa using hWrites) hWords
  refine ⟨hFinished.1, hFinished.2, ?_⟩
  intro saved words hOwner
  have hSeparate := allocated_region_disjoint heap.top 8 saved heap.nodes
    hOwner.buffer.rootBound hOwner.separated hOwner.below hFit
  refine ⟨(hOwner.arrayAllocated 8 1 hHeap hFit).writesRange hWrites ?_, hSeparate⟩
  simp only [regionsDisjoint, FreeNode.region, allocatedNode] at hSeparate
  have : (8 : UInt64).toNat = 8 := rfl
  omega

#print axioms emptyWords_owned
end Project.Drone.Execution
