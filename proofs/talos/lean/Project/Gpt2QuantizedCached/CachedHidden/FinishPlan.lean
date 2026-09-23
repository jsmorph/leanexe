import Project.Gpt2QuantizedCached.CachedHidden.Completion
import Project.Gpt2QuantizedCached.CachedHidden.Source

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def finishValue (status : UInt64) (hidden cache updates : ByteArray) : HiddenResult :=
  if status = 0 then ⟨0, hidden, cache ++ updates⟩ else ⟨status, .empty, .empty⟩

def finishHeap (heap : Heap) (status : UInt64) (cache updates : ByteArray) : Heap :=
  if status = 0 then heap.allocate (PackedAppend.need cache updates) else heap

def finishCacheNode (heap : Heap) (cache updates : ByteArray) : FreeNode :=
  allocatedNode heap.top (PackedAppend.need cache updates) heap.nodes

def cleanedHeap (heap : Heap) (embedding updates : FreeNode) : Heap :=
  (heap.release updates).release embedding

theorem finishValue_status (status : UInt64) (hidden cache updates : ByteArray) :
    (finishValue status hidden cache updates).status = status := by
  by_cases h : status = 0 <;> simp only [finishValue, h, ite_true, ite_false]

theorem cachedHidden_finish (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    cachedHidden weights cache token position =
      finishValue (layerPrefix weights cache token position 12).2.2
        (layerPrefix weights cache token position 12).1 cache
        (layerPrefix weights cache token position 12).2.1 := by
  rw [cachedHidden_eq]
  generalize layerPrefix weights cache token position 12 = state
  by_cases h : state.2.2 = 0 <;> simp only [finishValue, h, bne_self_eq_false, Bool.false_eq_true, ite_false,
    ite_true, bne_iff_ne, ne_eq, not_false_eq_true]

structure FinishMemory (before : Heap) (original : Store Unit) (heap : Heap) (current : Store Unit)
    (status : UInt64) (embeddingNode updatesNode hiddenNode cacheNode : FreeNode)
    (embeddingBytes updatesBytes hiddenBytes cacheBytes : ByteArray) : Prop
    extends Completion before original heap current status hiddenNode cacheNode hiddenBytes cacheBytes where
  embeddingOwned : heap.OwnsPacked current embeddingNode embeddingBytes
  updatesOwned : heap.OwnsPacked current updatesNode updatesBytes
  embeddingFresh : before.FreshNode embeddingNode
  updatesFresh : before.FreshNode updatesNode
  temporarySep : regionsDisjoint updatesNode.region embeddingNode.region
  hiddenEmbedding : status = 0 → regionsDisjoint hiddenNode.region embeddingNode.region
  hiddenUpdates : status = 0 → regionsDisjoint hiddenNode.region updatesNode.region
  cacheEmbedding : status = 0 → regionsDisjoint cacheNode.region embeddingNode.region
  cacheUpdates : status = 0 → regionsDisjoint cacheNode.region updatesNode.region

#print axioms cachedHidden_finish
end Project.Gpt2QuantizedCached.CachedHidden
