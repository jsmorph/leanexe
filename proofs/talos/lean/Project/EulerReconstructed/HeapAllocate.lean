import Project.EulerReconstructed.Program
import Project.EulerRiemann.HeapAllocateExecute

namespace Project.EulerReconstructed.Execution
open Wasm Project.Runtime Project.ProofKit
open Project.EulerRiemann.Execution

theorem heap_allocation_program_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (need previous current capacity next result : UInt64) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 ∧
      bumpPages heap.top need ≤ store.memoryCap Project.EulerReconstructed.«module» 0)
    (hPages : store.mem.pages ≤ 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp Project.EulerReconstructed.«module» rest Q (heap.allocateStore store need)
        (FixedArraySearch.frame params saved tail need previous current capacity next
          (allocatedRoot heap.top need heap.nodes)) env) :
    wp Project.EulerReconstructed.«module» (FixedArrayAllocate.program start 7 ++ rest) Q store
      (FixedArraySearch.frame params saved tail need previous current capacity next result) env := by
  apply FixedArrayAllocate.program_spec Project.EulerReconstructed.«module» env store params saved tail start hStart
    heap.top need 7 previous current capacity next result heap.allocations heap.nodes
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals]) hHeap.freeList hBump hPages rfl
  intro previous current capacity next
  simpa only [allocated_shared, allocatedRoot_shared, FixedArrayAllocateNone.counted,
    Heap.allocateStore, countedStore] using hNext previous current capacity next

#print axioms heap_allocation_program_spec

end Project.EulerReconstructed.Execution
