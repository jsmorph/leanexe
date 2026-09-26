import Project.Gpt2QuantizedCached.CachedHidden.Traversal
import Project.Gpt2QuantizedCached.CachedHidden.FinishPlan

namespace Project.Gpt2QuantizedCached.CachedHidden
open Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.LayerNorm (AllocationFits)

def embeddingHeap (heap : Heap) : Heap := heap.allocate Embedding.need

def embeddingNode (heap : Heap) : FreeNode := allocatedNode heap.top Embedding.need heap.nodes

def traversed (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat) : Traversal :=
  traversal (embeddingHeap heap) (embeddingNode heap) weights cache token position 12

def cacheNode (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat) : FreeNode :=
  finishCacheNode (traversed heap weights cache token position).heap cache
    (layerPrefix weights cache token position 12).2.1

def finalHeap (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat) : Heap :=
  cleanedHeap (finishHeap (traversed heap weights cache token position).heap
    (layerPrefix weights cache token position 12).2.2 cache (layerPrefix weights cache token position 12).2.1)
    (embeddingNode heap) (traversed heap weights cache token position).updates

structure Resources (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position pageCap : Nat) : Prop where
  embedding : AllocationFits heap Embedding.need pageCap
  layers : TraversalResources (embeddingHeap heap) (embeddingNode heap) weights cache token position pageCap
  cache : (layerPrefix weights cache token position 12).2.2 = 0 →
    AllocationFits (traversed heap weights cache token position).heap
      (PackedAppend.need cache (layerPrefix weights cache token position 12).2.1) pageCap

end Project.Gpt2QuantizedCached.CachedHidden
