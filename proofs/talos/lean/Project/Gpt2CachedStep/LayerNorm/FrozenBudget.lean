import Project.Gpt2CachedStep.LayerNorm.FrozenResources
import Project.ProofKit.HeapGrowth

namespace Project.Gpt2CachedStep.Frozen.LayerNorm
open Project.ProofKit Project.EulerRiemann.Execution

theorem AllocationFits.of_bound {heap : Heap} {need : UInt64}
    (h : heap.top.toNat + 48 + need.toNat < 4294967296) : AllocationFits heap need 65536 :=
  fun _ => ⟨h, FixedArrayBump.requiredPages_le heap.top need h.le⟩

theorem budget (heap : Heap) (h : heap.top.toNat + 4096 < 4294967296) :
    Resources heap 1 65536 ∧ (finalHeap heap 1).top.toNat ≤ heap.top.toNat + 4096 := by
  have hMeans := heap.allocate_top_le (temporaryNeed 1)
  have hInverses := (meansHeap heap 1).allocate_top_le (temporaryNeed 1)
  have hOutput := (inversesHeap heap 1).allocate_top_le (outputNeed 1)
  have hTemporary : (temporaryNeed 1).toNat = 8 := rfl
  have hOutputNeed : (outputNeed 1).toNat = 3072 := rfl
  rw [← meansHeap] at hMeans
  rw [← inversesHeap] at hInverses
  rw [← outputHeap] at hOutput
  simp only [hTemporary, hOutputNeed] at hMeans hInverses hOutput
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · apply AllocationFits.of_bound
    rw [hTemporary]
    omega
  · apply AllocationFits.of_bound
    rw [hTemporary]
    omega
  · apply AllocationFits.of_bound
    rw [hOutputNeed]
    omega
  · simpa only [finalHeap, Heap.release_top] using (show (outputHeap heap 1).top.toNat ≤ heap.top.toNat + 4096 by omega)

#print axioms budget

end Project.Gpt2CachedStep.Frozen.LayerNorm
