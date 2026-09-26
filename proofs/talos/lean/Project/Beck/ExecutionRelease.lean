import Project.Beck.ExecutionHeap

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

theorem releaseWords_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (node : FreeNode) (words : Array UInt64)
    (hHeap : heap.At initial) (hOwner : heap.OwnsWords initial node words) :
    TerminatesWith env Project.Beck.«module» 39 initial [.i64 node.root]
      (fun final values => values = [] ∧ final = heap.releaseStore initial node ∧
        (heap.release node).At final) := by
  obtain ⟨hMagic, hRc, hCapacity, hKind, hStride, hMask⟩ := hOwner.buffer.fresh
  have hBounds := hOwner.buffer.values.1
  have hFits := hOwner.buffer.values.2.1
  have hCall := Project.Runtime.release_frees_fixed_array_zero_mask_full env
    Project.Beck.«module» 39 initial node.root (freeHead heap.nodes)
    heap.releases heap.frees words.size 1 (typeIdx := some 39) rfl (by decide)
    (by omega) (by decide) hOwner.buffer.rootBound (by omega) (by omega)
    hMagic hRc hKind hOwner.buffer.values.lengthRead hStride hMask
    (by simp [hHeap.globals, Heap.globals]) (by simp [hHeap.globals, Heap.globals])
    (by simp [hHeap.globals, Heap.globals])
  apply hCall.mono
  rintro final values ⟨hValues, hMem, hGlobals, hStore⟩
  have hGlobals' : final.globals =
      { globals := ((initial.globals.globals.set 4 (.i64 (heap.releases + 1))).set 5
        (.i64 (heap.frees + 1))).set 1 (.i64 node.root) } := congrArg Globals.mk hGlobals
  have hFinal : final = heap.releaseStore initial node := by
    rw [hStore, hMem, hGlobals']
    rfl
  refine ⟨hValues, hFinal, ?_⟩
  rw [hFinal]
  exact heap.release_at initial node hHeap hOwner.buffer.rootBound
    hOwner.buffer.addressBound hOwner.buffer.memoryBound hCapacity hOwner.below hOwner.separated


#print axioms releaseWords_exact

end Project.Beck.Execution
