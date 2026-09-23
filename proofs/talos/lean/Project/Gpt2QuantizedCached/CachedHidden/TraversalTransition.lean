import Project.Gpt2QuantizedCached.CachedHidden.TraversalState

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem traversalState_pending (initial final : Store Unit) (heap next : Heap)
    (embeddingNode hiddenNode updatesNode : FreeNode) (params : List Value)
    (hiddenBytes updatesBytes : ByteArray) (status : UInt64) (index : Nat) (result : Locals)
    (hResult : LayerFrame params embeddingNode.root (statusRoot status hiddenNode) updatesNode.root
      hiddenBytes.size updatesBytes.size status (index + 1) result)
    (hOutput : PendingOutput heap initial next final status hiddenNode updatesNode hiddenBytes updatesBytes) :
    TraversalStateAt initial heap embeddingNode params (hiddenBytes, updatesBytes, status)
      ⟨next, hiddenNode, updatesNode⟩ (index + 1) final result :=
  ⟨hResult, hOutput.heapAt, hOutput.hidden, hOutput.updates.buffer.values,
    hOutput.updates.payload_protects, fun _ => hOutput.updates, hOutput.frame,
    fun _ => hOutput.hiddenFresh, fun _ => hOutput.updatesFresh, fun _ => hOutput.separated,
    hOutput.pages, hOutput.capacity⟩

#print axioms traversalState_pending

theorem traversalState_transition (initial final : Store Unit) (heap : Heap) (embeddingNode : FreeNode)
    (params : List Value) (weights cache : ByteArray) (source : LayerState) (machine : Traversal) (position index : Nat) (result : Locals)
    (hZero : source.2.2 = 0)
    (hResult : LayerFrame params embeddingNode.root
      (statusRoot (cachedBlock weights source.1 cache index position).status
        (CachedBlock.hiddenNode machine.heap position))
      (updatesNode machine.heap position
        (CachedBlock.tensors weights source.1 cache index position)
        source.2.1
        (cachedBlock weights source.1 cache index position)).root
      (cachedBlock weights source.1 cache index position).hidden.size
      (source.2.1.size +
        (cachedBlock weights source.1 cache index position).cache.size)
      (cachedBlock weights source.1 cache index position).status
      (index + 1) result)
    (hOutput : PendingOutput heap initial
      (activeHeap machine.heap
        machine.hidden
        machine.updates position index
        (CachedBlock.tensors weights source.1 cache index position)
        source.2.1
        (cachedBlock weights source.1 cache index position))
      final (cachedBlock weights source.1 cache index position).status
      (CachedBlock.hiddenNode machine.heap position)
      (updatesNode machine.heap position
        (CachedBlock.tensors weights source.1 cache index position)
        source.2.1
        (cachedBlock weights source.1 cache index position))
      (cachedBlock weights source.1 cache index position).hidden
      (source.2.1 ++
        (cachedBlock weights source.1 cache index position).cache)) :
    TraversalStateAt initial heap embeddingNode params (layerStep weights cache position source index)
      (traversalStep machine weights cache source position index) (index + 1) final result := by
  rw [layerStep_zero _ _ _ _ _ hZero]
  simp only [traversalStep, hZero, ite_true]
  apply traversalState_pending initial final heap _ embeddingNode _ _ params _ _ _ index result
  · simpa only [ByteArray.size_append] using hResult
  · exact hOutput


#print axioms traversalState_transition
end Project.Gpt2QuantizedCached.CachedHidden
