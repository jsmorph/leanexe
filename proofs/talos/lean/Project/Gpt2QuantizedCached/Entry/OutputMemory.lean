import Project.Gpt2QuantizedCached.Entry.OutputResult

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem outputOwned (heap : Heap) (store : Store Unit) (cache logits node : FreeNode)
    (cacheBytes logitsBytes bytes : ByteArray) (rejected : Bool)
    (hCache : heap.OwnsPacked store cache cacheBytes) (hLogits : heap.OwnsPacked store logits logitsBytes)
    (hNode : heap.OwnsPacked store node bytes)
    (hCacheSep : regionsDisjoint node.region cache.region)
    (hLogitsSep : regionsDisjoint node.region logits.region) :
    (outputHeap heap cache logits rejected).OwnsPacked (outputStore heap store cache logits rejected) node bytes := by
  cases rejected
  · exact hNode
  · exact (hNode.released logits hLogits.buffer.rootBound
      (by have := hLogits.buffer.addressBound; omega) hLogitsSep).released cache hCache.buffer.rootBound
      (by have := hCache.buffer.addressBound; omega) hCacheSep

theorem outputHeap_top (heap : Heap) (cache logits : FreeNode) (rejected : Bool) :
    (outputHeap heap cache logits rejected).top = heap.top := by
  cases rejected <;> rfl

#print axioms outputOwned
end Project.Gpt2QuantizedCached.Entry
