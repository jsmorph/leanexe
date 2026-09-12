import Project.EulerRiemann.InitialAllocationExecute
import Project.EulerRiemann.HeapState

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime

theorem initial_allocateStore_eq (heap : Heap) (store : Store Unit) (need : UInt64)
    (hNone : takeFirstFitFrom 0 need heap.nodes = none) :
    heap.allocateStore store need =
      FixedArrayAllocateNone.counted (FixedArrayBump.allocated store heap.top need 7) heap.allocations := by
  simp only [Heap.allocateStore, allocatedStore, hNone]
  rfl

theorem initial_allocateHeap_eq (heap : Heap) (need : UInt64)
    (hNone : takeFirstFitFrom 0 need heap.nodes = none) :
    heap.allocate need =
      { heap with top := heap.top + 48 + need, allocations := heap.allocations + 1 } := by
  simp only [Heap.allocate, allocatedTop, allocatedNodes, hNone]

theorem initial_allocation_heap_spec (site : InitialAllocationSite)
    (env : HostEnv Unit) (store : Store Unit) (heap : Heap) (params saved tail : List Wasm.Value)
    (hStart : params.length + saved.length = site.capacityLocal)
    (need previous current capacity next result : UInt64)
    (hHeap : heap.At store) (hNone : takeFirstFitFrom 0 need heap.nodes = none)
    (hFit32 : heap.top.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages heap.top need ≤ store.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous : UInt64,
      (heap.allocate need).At (heap.allocateStore store need) →
      Project.Clob.FreshFixedArrayAt (heap.allocateStore store need) (heap.top + 48) need 7 →
      wp module rest Q (heap.allocateStore store need)
        (FixedArraySearch.frame params saved tail need previous 0 (heap.top + 48 + need)
          ((heap.top + 48 + need - 1) / 65536 + 1) (heap.top + 48)) env) :
    wp module (site.allocationProgram ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  have hBasic : takeFirstFit need heap.nodes = none := by
    rw [← takeFirstFitFrom_project 0 need heap.nodes, hNone]
    rfl
  have hNewHeap := heap.allocate_at store need hHeap (fun _ => hFit32)
  have hFresh : Project.Clob.FreshFixedArrayAt
      (heap.allocateStore store need) (heap.top + 48) need 7 := by
    change Project.Clob.FreshFixedArrayAt (allocatedStore store heap.top need heap.nodes)
      (heap.top + 48) need 7
    simpa only [allocatedRoot, allocatedCapacity, hNone] using
      allocated_fresh store heap.top need heap.nodes hHeap.freeList (fun _ => hFit32)
  apply initial_allocation_none_spec site env store params saved tail hStart heap.top need
    previous current capacity next result heap.allocations heap.nodes
  · simp [hHeap.globals, Heap.globals]
  · simp [hHeap.globals, Heap.globals]
  · simp [hHeap.globals, Heap.globals]
  · exact hHeap.freeList
  · exact hBasic
  · exact hFit32
  · exact hPages
  · exact hCap
  · intro previous
    simpa only [initial_allocateStore_eq heap store need hNone] using hNext previous hNewHeap hFresh

#print axioms initial_allocateStore_eq
#print axioms initial_allocateHeap_eq
#print axioms initial_allocation_heap_spec

end Project.EulerRiemann.Execution
