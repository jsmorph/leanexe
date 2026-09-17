import Project.SequenceSoftmax.Allocation
import Project.EulerRiemann.OutputBudget
import Project.EulerRiemann.HeapFrame

namespace Project.SequenceSoftmax.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
  UInt64Array ProofKit.Memory

theorem map_state (heap : Heap) (initial final : Store Unit) (output : Array UInt64)
    (pageLimit : Nat) (hHeap : heap.At initial) (hPages : initial.mem.pages ≤ pageLimit)
    (hNeed : (mapCapacity output.size).toNat = 8*(output.size+1))
    (hBump : takeFirstFitFrom 0 (mapCapacity output.size) heap.nodes = none →
      heap.top.toNat+48+(mapCapacity output.size).toNat < 4294967296 ∧
      heap.top.toNat+48+(mapCapacity output.size).toNat ≤ pageLimit*65536)
    (hOutput : At final (mapRoot heap output.size) output)
    (hWrites : WritesRange (mapAllocated heap initial output.size) final
      (mapRoot heap output.size).toNat ((mapRoot heap output.size).toNat+8*(output.size+1))) :
    (heap.allocate (mapCapacity output.size)).At final ∧
    (heap.allocate (mapCapacity output.size)).OwnsWords final
      (allocatedNode heap.top (mapCapacity output.size) heap.nodes) output ∧
    heap.Frame initial (heap.allocate (mapCapacity output.size)) final ∧
    final.mem.pages ≤ pageLimit ∧
    (∀ m index, final.memoryCap m index = initial.memoryCap m index) := by
  obtain ⟨hFinalHeap, hOwner⟩ := heap.finishWords initial final (mapCapacity output.size) output
    hHeap (by omega) (fun h => (hBump h).1) hWrites hOutput
  refine ⟨hFinalHeap, hOwner, ?_, ?_, ?_⟩
  · exact heap.frame_arrayWritten initial final (mapCapacity output.size) 1 output.size hHeap
      (by omega) (fun h => (hBump h).1.le) hWrites
  · rw [hWrites.2.1]
    exact heap.allocateArrayStore_pages_bound initial (mapCapacity output.size) 1 pageLimit
      hPages (fun h => (hBump h).2)
  · intro m index
    rw [hWrites.1]
    exact heap.allocateArrayStore_memoryCap initial (mapCapacity output.size) 1 m index

#print axioms map_state

theorem map_finish (module_ : Wasm.Module) (heap : Heap) (initial final : Store Unit)
    (output : Array UInt64) (remaining pageLimit : Nat) (hHeap : heap.At initial)
    (hBudget : OutputBudget initial heap (48+(mapCapacity output.size).toNat+remaining) pageLimit module_)
    (hNeed : (mapCapacity output.size).toNat = 8*(output.size+1))
    (hOutput : At final (mapRoot heap output.size) output)
    (hWrites : WritesRange (mapAllocated heap initial output.size) final
      (mapRoot heap output.size).toNat ((mapRoot heap output.size).toNat+8*(output.size+1))) :
    (heap.allocate (mapCapacity output.size)).At final ∧
    (heap.allocate (mapCapacity output.size)).OwnsWords final
      (allocatedNode heap.top (mapCapacity output.size) heap.nodes) output ∧
    heap.Frame initial (heap.allocate (mapCapacity output.size)) final ∧
    OutputBudget final (heap.allocate (mapCapacity output.size)) remaining pageLimit module_ := by
  have hAddress := hBudget.addressBound
  have hMemory := hBudget.heapPages
  obtain ⟨hFinalHeap, hOwner, hPreserved, _, _⟩ := map_state heap initial final output pageLimit
    hHeap hBudget.pages hNeed (by intro _; constructor <;> omega) hOutput hWrites
  exact ⟨hFinalHeap, hOwner, hPreserved,
    hBudget.allocated (mapCapacity output.size) 1 remaining (by omega) hWrites⟩

#print axioms map_finish
end Project.SequenceSoftmax.Spec
