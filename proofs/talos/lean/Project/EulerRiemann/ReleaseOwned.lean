import Project.EulerRiemann.HeapGrid

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime

theorem release_owned (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (node : FreeNode) (grid : Array Traversal.Cell)
    (hHeap : heap.At initial) (hOwner : heap.Owns initial node grid) :
    TerminatesWith env Project.EulerRiemann.«module» 100 initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) := by
  have hCall := release_exact env initial node.root node.capacity (freeHead heap.nodes)
    heap.releases heap.frees grid hOwner.buffer.rootBound hOwner.buffer.fresh hOwner.buffer.values
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
  apply hCall.mono
  rintro final values ⟨rfl, hFinal⟩
  subst final
  exact ⟨rfl, rfl, heap.release_at initial node hHeap hOwner.buffer.rootBound
    hOwner.buffer.addressBound hOwner.buffer.memoryBound hOwner.buffer.fresh.2.2.1
    hOwner.below hOwner.separated⟩

#print axioms release_owned

end Project.EulerRiemann.Execution
