import Project.Gpt2QuantizedCached.CachedHidden.Traversal
import Project.Gpt2QuantizedCached.CachedHidden.LayerBudget
import Project.Gpt2QuantizedCached.CachedBlock.SourceOutputs

namespace Project.Gpt2QuantizedCached.CachedHidden
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def traversalBudget : Nat → Nat
  | 0 => 0
  | index + 1 => traversalBudget index + layerBudget index

theorem traversalBudget_mono {left right : Nat} (h : left ≤ right) :
    traversalBudget left ≤ traversalBudget right := by
  induction right, h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ right _ ih => exact ih.trans (Nat.le_add_right _ _)

theorem traversalBudget_twelve : traversalBudget 12 = 1659552 := rfl

theorem traversal_top (heap : Heap) (embeddingNode : FreeNode) (weights cache : ByteArray)
    (token : UInt32) (position count : Nat) (hPosition : position < 128) (hCount : count ≤ 12)
    (hBound : heap.top.toNat + traversalBudget count < 4294967296) :
    (traversal heap embeddingNode weights cache token position count).heap.top.toNat ≤
      heap.top.toNat + traversalBudget count := by
  induction count with
  | zero => simp only [traversal, traversalBudget, Nat.add_zero, Nat.le_refl]
  | succ index ih =>
    have hIndex : index < 12 := by omega
    have hBudget : traversalBudget index ≤ traversalBudget (index + 1) :=
      traversalBudget_mono (Nat.le_succ index)
    have hPrevious := ih (by omega) (by omega)
    by_cases hZero : (layerPrefix weights cache token position index).2.2 = 0
    · have hSizes := (layerPrefix_valid weights cache token position index).success hZero
      have hCache := CachedBlock.cachedBlock_cache_le weights
        (layerPrefix weights cache token position index).1 cache index position hSizes.1
      have hLayer := layerBudget_spec
        (traversal heap embeddingNode weights cache token position index).heap position index
        (CachedBlock.tensors weights (layerPrefix weights cache token position index).1 cache index position)
        (layerPrefix weights cache token position index).2.1
        (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position)
        (traversal heap embeddingNode weights cache token position index).hidden
        (traversal heap embeddingNode weights cache token position index).updates
        hPosition hIndex hSizes.2.le hCache (by
          simp only [traversalBudget] at hBound
          omega)
      simp only [traversal, traversalStep, hZero, ite_true]
      simpa only [traversalBudget, Nat.add_assoc] using
        hLayer.2.trans (Nat.add_le_add_right hPrevious (layerBudget index))
    · simp only [traversal, traversalStep, hZero, ite_false]
      exact hPrevious.trans (Nat.add_le_add_left hBudget _)

theorem traversalResources (heap : Heap) (embeddingNode : FreeNode) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (hPosition : position < 128)
    (hBound : heap.top.toNat + 1659552 < 4294967296) :
    TraversalResources heap embeddingNode weights cache token position 65536 := by
  constructor
  intro index hIndex hZero
  have hBudget := traversalBudget_mono (show index + 1 ≤ 12 by omega)
  rw [traversalBudget_twelve] at hBudget
  have hPrevious := traversal_top heap embeddingNode weights cache token position index hPosition
    (by omega) (by simp only [traversalBudget] at hBudget; omega)
  have hSizes := (layerPrefix_valid weights cache token position index).success hZero
  apply (layerBudget_spec (traversal heap embeddingNode weights cache token position index).heap position index
    (CachedBlock.tensors weights (layerPrefix weights cache token position index).1 cache index position)
    (layerPrefix weights cache token position index).2.1
    (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position)
    (traversal heap embeddingNode weights cache token position index).hidden
    (traversal heap embeddingNode weights cache token position index).updates
    hPosition hIndex hSizes.2.le
    (CachedBlock.cachedBlock_cache_le weights (layerPrefix weights cache token position index).1
      cache index position hSizes.1) ?_).1
  simp only [traversalBudget] at hBudget
  omega

#print axioms traversal_top
#print axioms traversalResources
end Project.Gpt2QuantizedCached.CachedHidden
