import Project.Drone.ExecutionHeap

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def emptyWordsStore (heap : Heap) (store : Store Unit) : Store Unit :=
  FixedArrayResult.writeLength (heap.allocateArrayStore store 8 1)
    (allocatedRoot heap.top 8 heap.nodes) 0

theorem emptyWords_memory (heap : Heap) (store : Store Unit) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 8 heap.nodes = none → heap.top.toNat + 48 + 8 < 4294967296) :
    Memory.WritesRange (heap.allocateArrayStore store 8 1) (emptyWordsStore heap store)
      (allocatedRoot heap.top 8 heap.nodes).toNat
      ((allocatedRoot heap.top 8 heap.nodes).toNat + 8) ∧
      UInt64Array.At (emptyWordsStore heap store) (allocatedRoot heap.top 8 heap.nodes) #[] := by
  have hFit : takeFirstFitFrom 0 8 heap.nodes = none →
      heap.top.toNat + 48 + (8 : UInt64).toNat ≤ 4294967296 := fun h => (hBump h).le
  have hBounds := allocated_bounds store heap.top 8 heap.nodes hHeap.freeList hFit
  have hCapacity := allocated_capacity (8 : UInt64) heap.nodes
  have hAddress : (allocatedRoot heap.top 8 heap.nodes).toNat + 8 ≤ 4294967296 := by
    have : (8 : UInt64).toNat = 8 := rfl
    omega
  have hMemory : (allocatedRoot heap.top 8 heap.nodes).toNat + 8 ≤
      (heap.allocateArrayStore store 8 1).mem.pages * 65536 := by
    change (allocatedRoot heap.top 8 heap.nodes).toNat + 8 ≤
      (FixedArrayAllocate.allocated store heap.top 8 1 heap.nodes).mem.pages * 65536
    rw [arrayAllocated_pages]
    have : (8 : UInt64).toNat = 8 := rfl
    omega
  have hWrites : Memory.WritesRange (heap.allocateArrayStore store 8 1)
      (emptyWordsStore heap store) (allocatedRoot heap.top 8 heap.nodes).toNat
      ((allocatedRoot heap.top 8 heap.nodes).toNat + 8) := by
    apply Memory.WritesRange.write64
    all_goals
      rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
  have hWords := FixedArrayResult.emptyStore_at
    (heap.allocateArrayStore store 8 1) (allocatedRoot heap.top 8 heap.nodes) hAddress hMemory
  exact ⟨hWrites, hWords⟩

#print axioms emptyWords_memory
end Project.Drone.Execution
