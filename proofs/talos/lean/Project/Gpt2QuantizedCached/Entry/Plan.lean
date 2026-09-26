import Project.Gpt2QuantizedCached.Entry.AcceptedSource

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def outputCacheNode (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat) : FreeNode :=
  CachedHidden.cacheNode heap weights cache token position

def outputLogitsNode (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat) : FreeNode :=
  vocabularyNode (normalizationHeap (CachedHidden.finalHeap heap weights cache token position))

def acceptedHeap (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position : Nat) : Heap :=
  hiddenStageHeap (CachedHidden.finalHeap heap weights cache token position)
    (CachedHidden.traversed heap weights cache token position).hidden (outputCacheNode heap weights cache token position)
    weights (cachedHidden weights cache token position) position

structure Resources (heap : Heap) (weights cache : ByteArray) (token : UInt32) (position pageCap : Nat) : Prop where
  hidden : CachedHidden.Resources heap weights cache token position pageCap
  normalized : Gpt2CachedStep.LayerNorm.Resources (CachedHidden.finalHeap heap weights cache token position) 1 pageCap
  logits : GroupedProjection.Projection.Resources
    (normalizationHeap (CachedHidden.finalHeap heap weights cache token position)) 768 50257 1 pageCap

end Project.Gpt2QuantizedCached.Entry
