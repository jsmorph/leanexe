import Project.Gpt2QuantizedCached.Entry.StageBudget

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def stepBudget (cacheSize : Nat) : Nat := CachedHidden.hiddenBudget cacheSize + tailBudget

theorem stepBudget_value (cacheSize : Nat) : stepBudget cacheSize = 1942544 + cacheSize := by
  rw [stepBudget, tailBudget_value]
  unfold CachedHidden.hiddenBudget
  omega

theorem accepted_budget (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (hPosition : position < 128) (hBound : heap.top.toNat + stepBudget cache.size < 4294967296) :
    Resources heap weights cache token position 65536 ∧
      (acceptedHeap heap weights cache token position).top.toNat ≤ heap.top.toNat + stepBudget cache.size := by
  have hHidden := CachedHidden.budget heap weights cache token position hPosition
    (by unfold stepBudget at hBound; omega)
  have hTail := tail_budget (CachedHidden.finalHeap heap weights cache token position)
    (CachedHidden.traversed heap weights cache token position).hidden (outputCacheNode heap weights cache token position)
    weights (cachedHidden weights cache token position) position
    (by unfold stepBudget at hBound; omega)
  refine ⟨⟨hHidden.1, hTail.1, hTail.2.1⟩, ?_⟩
  change (hiddenStageHeap (CachedHidden.finalHeap heap weights cache token position)
    (CachedHidden.traversed heap weights cache token position).hidden (outputCacheNode heap weights cache token position)
    weights (cachedHidden weights cache token position) position).top.toNat ≤ _
  unfold stepBudget
  exact hTail.2.2.trans (Nat.add_le_add_right hHidden.2 _ |>.trans_eq (Nat.add_assoc ..))

theorem selectHeap_top (rejected : Bool) (before after : Heap) (bound : Nat)
    (hBefore : before.top.toNat ≤ bound) (hAfter : after.top.toNat ≤ bound) :
    (selectHeap rejected before after).top.toNat ≤ bound := by
  cases rejected
  · exact hAfter
  · exact hBefore

theorem budget (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (hBound : heap.top.toNat + stepBudget cache.size < 4294967296) :
    (invalidInput cache token position = false → Resources heap weights cache token position 65536) ∧
      (finalHeap heap weights cache token position).top.toNat ≤ heap.top.toNat + stepBudget cache.size := by
  have hResources (hValid : invalidInput cache token position = false) :=
    accepted_budget heap weights cache token position ((invalidInput_false cache token position).mp hValid).2.1 hBound
  refine ⟨fun h => (hResources h).1, ?_⟩
  unfold finalHeap
  apply selectHeap_top _ _ _ _ (Nat.le_add_right ..)
  unfold inputHeap selectHeap
  cases hValid : invalidInput cache token position
  · simp only [Bool.false_eq_true, ite_false]
    unfold cacheHeap
    exact selectHeap_top _ _ _ _ (Nat.le_add_right ..) (hResources hValid).2
  · simp only [ite_true]
    exact Nat.le_add_right ..

#print axioms accepted_budget
#print axioms budget
end Project.Gpt2QuantizedCached.Entry
