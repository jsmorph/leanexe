import Project.Gpt2CachedStep.CachedAttention.FrozenResources
import Project.Gpt2CachedStep.LayerNorm.FrozenBudget

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Project.ProofKit Project.EulerRiemann.Execution

theorem scoresNeed_le (position : Nat) (hPosition : position < 128) :
    (scoresNeed position).toNat ≤ 6152 := by
  rw [scoresNeed, PackedCapacity.capacity_toNat _ (by omega)]
  exact (PackedCapacity.capacityNat_le _).trans (by omega)

theorem budget (heap : Heap) (position : Nat) (hPosition : position < 128)
    (h : heap.top.toNat + 24576 < 4294967296) :
    Resources heap position 65536 ∧ (finalHeap heap position).top.toNat ≤ heap.top.toNat + 24576 := by
  have hScores := heap.allocate_top_le (scoresNeed position)
  have hMaxima := (scoresHeap heap position).allocate_top_le maximaNeed
  have hExponentials := (maximaHeap heap position).allocate_top_le (scoresNeed position)
  have hSums := (exponentialsHeap heap position).allocate_top_le maximaNeed
  have hProbabilities := (sumsHeap heap position).allocate_top_le (scoresNeed position)
  have hOutput := (probabilitiesHeap heap position).allocate_top_le mixedNeed
  have hScoreNeed := scoresNeed_le position hPosition
  have hMaximaNeed : maximaNeed.toNat = 48 := rfl
  have hMixedNeed : mixedNeed.toNat = 3072 := rfl
  rw [← scoresHeap] at hScores
  rw [← maximaHeap] at hMaxima
  rw [← exponentialsHeap] at hExponentials
  rw [← sumsHeap] at hSums
  rw [← probabilitiesHeap] at hProbabilities
  rw [← outputHeap] at hOutput
  simp only [hMaximaNeed, hMixedNeed] at hScores hMaxima hExponentials hSums hProbabilities hOutput
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first
    | (apply LayerNorm.AllocationFits.of_bound; omega)
    | (simp only [finalHeap, cleanupHeap, Heap.release_top]; omega)

#print axioms budget

end Project.Gpt2CachedStep.Frozen.CachedAttention
