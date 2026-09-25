import Project.Gpt2CachedStep.Entry.FrozenCode

namespace Project.Gpt2CachedStep.Frozen.Entry
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def hiddenHeap (heap : Heap) (position cacheSize : Nat) : Heap := CachedHidden.finalHeap heap position cacheSize
def hiddenNode (heap : Heap) (position : Nat) : FreeNode := (CachedHidden.traversed heap position).hidden
def cacheNode (heap : Heap) (position cacheSize : Nat) : FreeNode := CachedHidden.cacheNode heap position cacheSize
def normalizedHeap (heap : Heap) (position cacheSize : Nat) : Heap := LayerNorm.finalHeap (hiddenHeap heap position cacheSize) 1
def normalizedNode (heap : Heap) (position cacheSize : Nat) : FreeNode := LayerNorm.outputNode (hiddenHeap heap position cacheSize) 1
def logitsNode (heap : Heap) (position cacheSize : Nat) : FreeNode :=
  allocatedNode (normalizedHeap heap position cacheSize).top Vocabulary.outputNeed (normalizedHeap heap position cacheSize).nodes
def logitsHeap (heap : Heap) (position cacheSize : Nat) : Heap :=
  (normalizedHeap heap position cacheSize).allocate Vocabulary.outputNeed
def finalHeap (heap : Heap) (position cacheSize : Nat) : Heap :=
  ((logitsHeap heap position cacheSize).release (normalizedNode heap position cacheSize)).release (hiddenNode heap position)

structure Resources (heap : Heap) (position cacheSize pageCap : Nat) : Prop where
  hidden : CachedHidden.Resources heap position cacheSize pageCap
  normalization : LayerNorm.Resources (hiddenHeap heap position cacheSize) 1 pageCap
  logits : LayerNorm.AllocationFits (normalizedHeap heap position cacheSize) Vocabulary.outputNeed pageCap

def normalized (weights cache : ByteArray) (token : UInt32) (position : Nat) : ByteArray :=
  layerNorm weights (cachedHidden weights cache token position).hidden finalNormOffset (finalNormOffset + 768) 1

theorem normalized_size (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    (normalized weights cache token position).size = 3072 := LayerNorm.layerNorm_size ..

theorem cachedStep_valid {weights cache : ByteArray} {token : UInt32} {position : Nat}
    (h : Valid weights cache token position) : cachedStep weights cache token position =
      { cache := (cachedHidden weights cache token position).cache,
        logits := vocabularyHead weights (normalized weights cache token position) } := by
  have hCacheSize : cache.size = position * cachePositionWords * 4 := by rw [h.2.2.2, Nat.mul_assoc]; rfl
  simp [cachedStep, h.1, vocabulary, Nat.not_le.mpr h.2.1, Nat.not_le.mpr h.2.2.1, hCacheSize, normalized]

end Project.Gpt2CachedStep.Frozen.Entry
