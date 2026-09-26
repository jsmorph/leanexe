import Project.Gpt2QuantizedCached.Entry.FrontPlan

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def tailBudget : Nat := 4096 + GroupedProjection.Projection.allocationBudget 768 50257 1

theorem tailBudget_value : tailBudget = 206088 := rfl

theorem normalizedTail_top (heap : Heap) (cache normalizedNode : FreeNode)
    (weights outputCache normalized : ByteArray) (position : Nat) :
    (normalizedTailHeap heap cache normalizedNode weights outputCache normalized position).top.toNat ≤
      heap.top.toNat + GroupedProjection.Projection.allocationBudget 768 50257 1 := by
  have hProjection := GroupedProjection.Projection.outputHeap_top heap 768 50257 1
  simp only [normalizedTailHeap, Heap.release_top]
  split
  · simpa only [vocabularyHeap, outputHeap_top] using hProjection
  · simp only [Heap.release_top]
    omega

theorem normalization_budget (heap : Heap) (hBound : heap.top.toNat + 4096 < 4294967296) :
    Gpt2CachedStep.LayerNorm.Resources heap 1 65536 ∧
      (normalizationHeap heap).top.toNat ≤ heap.top.toNat + 4096 := by
  unfold normalizationHeap
  exact Gpt2CachedStep.LayerNorm.budget heap hBound

theorem normalizedStage_top (heap : Heap) (cacheNode : FreeNode)
    (weights hidden outputCache : ByteArray) (position : Nat)
    (hTop : (normalizationHeap heap).top.toNat ≤ heap.top.toNat + 4096) :
    (normalizedStageHeap heap cacheNode weights hidden outputCache position).top.toNat ≤
      heap.top.toNat + tailBudget := by
  unfold normalizedStageHeap
  exact (normalizedTail_top (normalizationHeap heap) cacheNode (normalizationNode heap)
    weights outputCache (normalizedBytes weights hidden) position).trans
      ((Nat.add_le_add_right hTop _).trans_eq (Nat.add_assoc ..))

theorem hiddenStage_top (heap : Heap) (hiddenNode cacheNode : FreeNode)
    (weights : ByteArray) (hidden : HiddenResult) (position : Nat)
    (hStage : (normalizedStageHeap heap cacheNode weights hidden.hidden hidden.cache position).top.toNat ≤
      heap.top.toNat + tailBudget) :
    (hiddenStageHeap heap hiddenNode cacheNode weights hidden position).top.toNat ≤
      heap.top.toNat + tailBudget := by
  unfold hiddenStageHeap
  split
  · rw [Heap.release_top]
    exact hStage
  · exact Nat.le_add_right ..

theorem tail_budget (heap : Heap) (hiddenNode cacheNode : FreeNode)
    (weights : ByteArray) (hidden : HiddenResult) (position : Nat)
    (hBound : heap.top.toNat + tailBudget < 4294967296) :
    Gpt2CachedStep.LayerNorm.Resources heap 1 65536 ∧
    GroupedProjection.Projection.Resources (normalizationHeap heap) 768 50257 1 65536 ∧
    (hiddenStageHeap heap hiddenNode cacheNode weights hidden position).top.toNat ≤
      heap.top.toNat + tailBudget := by
  have hNorm := normalization_budget heap (by unfold tailBudget at hBound; omega)
  have hProjectionBound : (normalizationHeap heap).top.toNat +
      GroupedProjection.Projection.allocationBudget 768 50257 1 < 4294967296 :=
    lt_of_le_of_lt ((Nat.add_le_add_right hNorm.2 _).trans_eq (Nat.add_assoc ..)) hBound
  exact ⟨hNorm.1, GroupedProjection.Projection.budget _ _ _ _ hProjectionBound,
    hiddenStage_top heap hiddenNode cacheNode weights hidden position
      (normalizedStage_top heap cacheNode weights hidden.hidden hidden.cache position hNorm.2)⟩

#print axioms normalization_budget
#print axioms normalizedStage_top
#print axioms hiddenStage_top
#print axioms tail_budget
end Project.Gpt2QuantizedCached.Entry
