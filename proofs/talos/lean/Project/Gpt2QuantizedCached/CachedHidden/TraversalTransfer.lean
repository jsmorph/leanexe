import Project.Gpt2QuantizedCached.CachedHidden.TraversalTransition

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem traversalState_active (initial final : Store Unit) (heap : Heap) (embeddingNode : FreeNode)
    (params : List Value) (weights cache : ByteArray) (token : UInt32) (position index : Nat) (result : Locals)
    (hZero : (layerPrefix weights cache token position index).2.2 = 0)
    (hResult : LayerFrame params embeddingNode.root
      (statusRoot (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position).status
        (CachedBlock.hiddenNode (traversal heap embeddingNode weights cache token position index).heap position))
      (updatesNode (traversal heap embeddingNode weights cache token position index).heap position
        (CachedBlock.tensors weights (layerPrefix weights cache token position index).1 cache index position)
        (layerPrefix weights cache token position index).2.1
        (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position)).root
      (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position).hidden.size
      ((layerPrefix weights cache token position index).2.1.size +
        (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position).cache.size)
      (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position).status
      (index + 1) result)
    (hOutput : PendingOutput heap initial
      (activeHeap (traversal heap embeddingNode weights cache token position index).heap
        (traversal heap embeddingNode weights cache token position index).hidden
        (traversal heap embeddingNode weights cache token position index).updates position index
        (CachedBlock.tensors weights (layerPrefix weights cache token position index).1 cache index position)
        (layerPrefix weights cache token position index).2.1
        (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position))
      final (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position).status
      (CachedBlock.hiddenNode (traversal heap embeddingNode weights cache token position index).heap position)
      (updatesNode (traversal heap embeddingNode weights cache token position index).heap position
        (CachedBlock.tensors weights (layerPrefix weights cache token position index).1 cache index position)
        (layerPrefix weights cache token position index).2.1
        (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position))
      (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position).hidden
      ((layerPrefix weights cache token position index).2.1 ++
        (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position).cache)) :
    TraversalState initial heap embeddingNode params weights cache token position (index + 1) final result := by
  unfold TraversalState
  rw [layerPrefix_succ, traversal]
  exact traversalState_transition initial final heap embeddingNode params weights cache
    (layerPrefix weights cache token position index)
    (traversal heap embeddingNode weights cache token position index) position index result hZero hResult hOutput

#print axioms traversalState_active
end Project.Gpt2QuantizedCached.CachedHidden
