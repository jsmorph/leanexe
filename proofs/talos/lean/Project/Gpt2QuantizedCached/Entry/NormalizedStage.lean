import Project.Gpt2QuantizedCached.Entry.NormalizedTail
import Project.Gpt2CachedStep.LayerNorm.Fresh

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def normalizedBytes (weights hidden : ByteArray) : ByteArray :=
  LeanExe.Models.Gpt2.layerNorm weights hidden (finalNormOffset / 4) (finalNormOffset / 4 + 768) 1

def normalizationHeap (heap : Heap) : Heap := Gpt2CachedStep.LayerNorm.finalHeap heap 1

def normalizationNode (heap : Heap) : FreeNode := Gpt2CachedStep.LayerNorm.outputNode heap 1

def normalizedStageHeap (heap : Heap) (cache : FreeNode) (weights hidden outputCache : ByteArray) (position : Nat) : Heap :=
  normalizedTailHeap (normalizationHeap heap) cache (normalizationNode heap)
    weights outputCache (normalizedBytes weights hidden) position

set_option maxRecDepth 32768 in
theorem hiddenBody_parts : hiddenBody = normalizedCode ++ normalizedTailCode := rfl

theorem normalizedStage_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (hiddenNode cacheNode : FreeNode)
    (weights cache hidden outputCache : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hHidden : heap.OwnsPacked initial hiddenNode hidden) (hCache : heap.OwnsPacked initial cacheNode outputCache)
    (hCacheFresh : before.FreshNode cacheNode) (hHiddenCache : regionsDisjoint hiddenNode.region cacheNode.region)
    (hFrame : before.Frame original heap initial)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hHeader : validHeader weights = true) (hHiddenSize : hidden.size = 3072)
    (hCacheSize : (position + 1) * cachePositionWords * 4 ≤ outputCache.size) (hPosition : position < 128)
    (hNormResources : Gpt2CachedStep.LayerNorm.Resources heap 1 (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hProjectionResources : GroupedProjection.Projection.Resources (normalizationHeap heap) 768 50257 1
      (initial.memoryCap «module» 0))
    (hState : HiddenState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      0 hiddenNode.root cacheNode.root 3072 outputCache.size frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let output := normalizedResult weights outputCache (normalizedBytes weights hidden) position
      ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status cacheNode) (statusRoot output.status (vocabularyNode (normalizationHeap heap)))
        output.cache.size output.logits.size result →
      result.locals[17]? = some (.i64 hiddenNode.root) →
      Completion before original (normalizedStageHeap heap cacheNode weights hidden outputCache position)
        final output.status cacheNode (vocabularyNode (normalizationHeap heap)) output.cache output.logits →
      (normalizedStageHeap heap cacheNode weights hidden outputCache position).OwnsPacked final hiddenNode hidden →
      (output.status = 0 → regionsDisjoint hiddenNode.region (vocabularyNode (normalizationHeap heap)).region) →
      wp «module» rest Q final result env) :
    wp «module» (hiddenBody ++ rest) Q initial frame env := by
  rw [hiddenBody_parts, List.append_assoc]
  apply normalized_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr hiddenNode.root cacheNode.root
    weights cache hidden token position outputCache.size frame hHeap hWeights hHidden.buffer.values
    hWeightsProtected hHidden.payload_protects hHeader hHiddenSize hNormResources hPages hState
  intro normalized prepared hPrepared hNextHeap hNormalized hStep hNextPages hStepCap
  have hCap' : normalized.memoryCap «module» 0 = initial.memoryCap «module» 0 := hStepCap
  have hResources : GroupedProjection.Projection.Resources (normalizationHeap heap) 768 50257 1
      (normalized.memoryCap «module» 0) := by rw [hCap']; exact hProjectionResources
  have hFresh := Gpt2CachedStep.LayerNorm.outputNode_fresh hNormResources
  apply normalizedTail_spec env original normalized before (normalizationHeap heap) weightsOwner weightsPtr cacheOwner cachePtr
    hiddenNode cacheNode (normalizationNode heap) weights cache hidden outputCache (normalizedBytes weights hidden)
    token position prepared hNextHeap (hStep.packed hWeightsProtected hWeights)
    (hStep.protects _ _ hWeightsProtected) (hStep.ownsPacked hNextHeap hHidden) (hStep.ownsPacked hNextHeap hCache)
    hNormalized hCacheFresh (hFrame.freshNode hFresh) hHiddenCache
    (regionsDisjoint_symm (hFresh.owns_disjoint hNormalized.buffer.rootBound hHidden))
    (hFresh.owns_disjoint hNormalized.buffer.rootBound hCache) (hFrame.trans hStep) hNextPages
    (hCap'.trans hCap) hHeader (by unfold normalizedBytes; rw [Gpt2CachedStep.LayerNorm.layerNorm_size])
    hCacheSize hPosition hResources hPrepared
  exact hNext

#print axioms normalizedStage_spec
end Project.Gpt2QuantizedCached.Entry
