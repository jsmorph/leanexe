import Project.Gpt2QuantizedCached.CachedHidden.Sizes
import Project.Gpt2QuantizedCached.CachedHidden.LayerPlan

namespace Project.Gpt2QuantizedCached.CachedHidden
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

structure Traversal where
  heap : Heap
  hidden : FreeNode
  updates : FreeNode

def traversalStep (state : Traversal) (weights cache : ByteArray) (source : LayerState)
    (position layer : Nat) : Traversal :=
  if source.2.2 = 0 then
    let values := CachedBlock.tensors weights source.1 cache layer position
    let output := cachedBlock weights source.1 cache layer position
    { heap := activeHeap state.heap state.hidden state.updates position layer values source.2.1 output
      hidden := CachedBlock.hiddenNode state.heap position
      updates := updatesNode state.heap position values source.2.1 output }
  else state

def traversal (heap : Heap) (embeddingNode : FreeNode) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) : Nat → Traversal
  | 0 => ⟨heap, embeddingNode, ⟨0, 0⟩⟩
  | layer + 1 => traversalStep (traversal heap embeddingNode weights cache token position layer)
      weights cache (layerPrefix weights cache token position layer) position layer

structure TraversalResources (heap : Heap) (embeddingNode : FreeNode) (weights cache : ByteArray)
    (token : UInt32) (position pageCap : Nat) : Prop where
  layer : ∀ index < 12, (layerPrefix weights cache token position index).2.2 = 0 →
    LayerResources (traversal heap embeddingNode weights cache token position index).heap position
      (CachedBlock.tensors weights (layerPrefix weights cache token position index).1 cache index position)
      (layerPrefix weights cache token position index).2.1
      (cachedBlock weights (layerPrefix weights cache token position index).1 cache index position) pageCap

theorem ValidState.success {count : Nat} {state : LayerState} (h : ValidState count state)
    (hZero : state.2.2 = 0) : state.1.size = 3072 ∧ state.2.1.size = count * 6144 := by
  rcases h with hSuccess | hFailure
  · exact hSuccess.2
  · have hImpossible := hFailure.1
    rw [hZero] at hImpossible
    contradiction

theorem ValidState.updates_le {count : Nat} {state : LayerState} (h : ValidState count state) :
    state.2.1.size ≤ count * 6144 := by
  rcases h with hSuccess | hFailure
  · exact hSuccess.2.2.le
  · exact hFailure.2.2

#print axioms ValidState.success
end Project.Gpt2QuantizedCached.CachedHidden
