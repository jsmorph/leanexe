import Project.Gpt2CachedStep.CachedHidden.Resources

namespace Project.Gpt2CachedStep.CachedHidden
open Project.Runtime Project.EulerRiemann.Execution

structure Traversal where
  heap : Heap
  hidden : FreeNode
  updates : FreeNode

def traversalStep (state : Traversal) (position layer : Nat) : Traversal :=
  { heap := stepHeap state.heap state.hidden state.updates position layer
    hidden := CachedBlock.hiddenNode state.heap position
    updates := updatesNode state.heap position layer }

def traversal (heap : Heap) (embedding : FreeNode) (position : Nat) : Nat → Traversal
  | 0 => ⟨heap, embedding, ⟨0, 0⟩⟩
  | layer + 1 => traversalStep (traversal heap embedding position layer) position layer

structure TraversalResources (heap : Heap) (embedding : FreeNode) (position pageCap : Nat) : Prop where
  layer : ∀ index < 12, LayerResources (traversal heap embedding position index).heap position index pageCap

end Project.Gpt2CachedStep.CachedHidden
