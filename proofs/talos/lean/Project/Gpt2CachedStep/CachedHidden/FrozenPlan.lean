import Project.Gpt2CachedStep.CachedHidden.FrozenTraversal
import Project.Gpt2CachedStep.CachedHidden.FrozenEmbedding

namespace Project.Gpt2CachedStep.Frozen.CachedHidden
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

def embeddingNode (heap : Heap) : FreeNode := allocatedNode heap.top embeddingNeed heap.nodes

def embeddingHeap (heap : Heap) : Heap := heap.allocate embeddingNeed

def traversed (heap : Heap) (position : Nat) : Traversal :=
  traversal (embeddingHeap heap) (embeddingNode heap) position 12

def cacheNeed (cacheSize : Nat) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (cacheSize + 73728))

def cacheNode (heap : Heap) (position cacheSize : Nat) : FreeNode :=
  allocatedNode (traversed heap position).heap.top (cacheNeed cacheSize) (traversed heap position).heap.nodes

def cacheHeap (heap : Heap) (position cacheSize : Nat) : Heap :=
  (traversed heap position).heap.allocate (cacheNeed cacheSize)

def finalHeap (heap : Heap) (position cacheSize : Nat) : Heap :=
  ((cacheHeap heap position cacheSize).release (traversed heap position).updates).release (embeddingNode heap)

structure Resources (heap : Heap) (position cacheSize pageCap : Nat) : Prop where
  embedding : LayerNorm.AllocationFits heap embeddingNeed pageCap
  layers : TraversalResources (embeddingHeap heap) (embeddingNode heap) position pageCap
  cache : LayerNorm.AllocationFits (traversed heap position).heap (cacheNeed cacheSize) pageCap

end Project.Gpt2CachedStep.Frozen.CachedHidden
