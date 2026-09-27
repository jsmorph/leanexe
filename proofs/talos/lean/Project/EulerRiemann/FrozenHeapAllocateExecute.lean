import Project.EulerRiemann.FrozenHeapState
import Project.ProofKit.FixedArrayAllocate

namespace Project.EulerRiemann.Frozen.Execution
open Wasm Project.Runtime Project.ProofKit

theorem allocated_shared (store : Store Unit) (base need : UInt64) (nodes : List FreeNode) :
    FixedArrayAllocate.allocated store base need 7 nodes = allocatedStore store base need nodes := rfl

theorem allocatedRoot_shared (base need : UInt64) (nodes : List FreeNode) :
    FixedArrayAllocate.root base need nodes = allocatedRoot base need nodes := rfl

theorem heap_allocation_program_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (need previous current capacity next result : UInt64) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp module rest Q (heap.allocateStore store need)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (allocatedRoot heap.top need heap.nodes)) env) :
    wp module (FixedArrayAllocate.program start 7 ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  apply FixedArrayAllocate.program_spec module env store params saved tail start hStart
    heap.top need 7 previous current capacity next result heap.allocations heap.nodes
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals]) hHeap.freeList hBump hPages rfl
  intro previous current capacity next
  simpa only [allocated_shared, allocatedRoot_shared, FixedArrayAllocateNone.counted,
    Heap.allocateStore, countedStore] using hNext previous current capacity next

#print axioms allocated_shared
#print axioms allocatedRoot_shared
#print axioms heap_allocation_program_spec

end Project.EulerRiemann.Frozen.Execution
