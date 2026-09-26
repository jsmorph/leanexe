import Project.Gpt2QuantizedCached.CachedBlock.Body
import Project.Gpt2QuantizedCached.CachedBlock.Budget

namespace Project.Gpt2QuantizedCached.CachedBlock
open Project.ProofKit Project.EulerRiemann.Execution

theorem executionHeap_top (heap : Heap) (position : Nat) (values : Tensors)
    (hPosition : position < 128) (h : heap.top.toNat + 98304 < 4294967296) :
    (executionHeap heap position values).top.toNat ≤ heap.top.toNat + 98304 := by
  have hTops := (budget_with_tops heap position hPosition h).2
  simp only [executionHeap, frontHeap, postAttentionHeap, feedForwardHeap, tailHeap, Heap.release_top, apply_ite]
  split
  · split
    · split
      · split
        · exact hTops.cache
        · exact hTops.activated
      · exact hTops.normalized2
    · exact hTops.attention
  · exact hTops.normalized

#print axioms executionHeap_top
end Project.Gpt2QuantizedCached.CachedBlock
