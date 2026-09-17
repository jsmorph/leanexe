import Project.SequenceSoftmax.Program
import Project.EulerRiemann.OwnedWords
import Project.ProofKit.FixedArrayRelease

namespace Project.SequenceSoftmax.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem release_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (node : FreeNode) (words : Array UInt64)
    (hHeap : heap.At initial) (hOwner : heap.OwnsWords initial node words) :
    TerminatesWith env module 15 initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) := by
  have hBounds := hOwner.buffer.values.1
  have hFits := hOwner.buffer.values.2.1
  apply (FixedArrayRelease.exact env module 15 initial node.root node.capacity
    (freeHead heap.nodes) heap.releases heap.frees words.size 1
    (typeIdx := some 15) rfl (by decide) (by omega) (by decide)
    hOwner.buffer.rootBound (by omega) (by omega) hOwner.buffer.fresh
    hOwner.buffer.values.lengthRead (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])).mono
  rintro final values ⟨hValues, rfl⟩
  exact ⟨hValues, rfl, heap.release_at initial node hHeap hOwner.buffer.rootBound
    hOwner.buffer.addressBound hOwner.buffer.memoryBound hOwner.buffer.fresh.2.2.1
    hOwner.below hOwner.separated⟩

#print axioms release_exact
end Project.SequenceSoftmax.Spec
