import Project.EulerRiemann.ArrayAllocationMemory

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ProofKit

theorem heap_array_allocation_program_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (need stride previous current capacity next result : UInt64) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap module 0)
    (hPages : store.mem.pages ≤ 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp module rest Q (heap.allocateArrayStore store need stride)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (allocatedRoot heap.top need heap.nodes)) env) :
    wp module (FixedArrayAllocate.program start stride ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  apply FixedArrayAllocate.program_spec module env store params saved tail start hStart
    heap.top need stride previous current capacity next result heap.allocations heap.nodes
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals]) hHeap.freeList hBump hPages rfl
  intro previous current capacity next
  simpa only [Heap.allocateArrayStore, allocatedRoot_shared] using hNext previous current capacity next

#print axioms heap_array_allocation_program_spec

end Project.EulerRiemann.Execution
