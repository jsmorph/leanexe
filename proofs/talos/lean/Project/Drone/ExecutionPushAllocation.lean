import Project.Drone.ExecutionHeap
import Project.ProofKit.WordArrayPushCapacity

namespace Project.Drone.Execution
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution WordArrayPush

def allocatedScratch (s : Scratch) (root previous current capacity next : UInt64) : Scratch :=
  { s with
    root := root
    previous := previous
    current := current
    capacity := capacity
    next := next }

theorem push_allocation_spec (env : HostEnv Unit) (store : Store Unit) (heap : Heap)
    (params saved tail : List Wasm.Value) (s : Scratch) (hHeap : heap.At store)
    (hBump : takeFirstFitFrom 0 s.need heap.nodes = none →
      heap.top.toNat + 48 + s.need.toNat ≤ 4294967296 ∧
      bumpPages heap.top s.need ≤ store.memoryCap Project.Drone.«module» 0)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp Project.Drone.«module» rest Q (heap.allocateArrayStore store s.need 1)
        (WordArrayPush.frame params saved tail
          (allocatedScratch s (allocatedRoot heap.top s.need heap.nodes) previous current capacity next)) env) :
    wp Project.Drone.«module» (FixedArrayAllocate.program (params.length + saved.length + 9) 1 ++ rest)
      Q store (WordArrayPush.frame params saved tail s) env := by
  rw [frame_as_search]
  apply array_allocation_spec env store heap params (allocationSaved saved s) tail _
    (by rw [allocationSaved_length]; omega) s.need 1 s.previous s.current s.capacity s.next s.root
    hHeap hBump hPages Q rest
  intro previous current capacity next
  simpa only [frame_as_search, allocatedScratch, allocationSaved] using
    hNext previous current capacity next

#print axioms push_allocation_spec
end Project.Drone.Execution
