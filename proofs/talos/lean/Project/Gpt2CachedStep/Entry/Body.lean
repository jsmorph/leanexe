import Project.Gpt2CachedStep.Entry.Hidden
import Project.Gpt2CachedStep.Entry.Normalized
import Project.Gpt2CachedStep.Entry.Logits
import Project.Gpt2CachedStep.Entry.Cleanup
import Project.Gpt2CachedStep.Entry.Plan

namespace Project.Gpt2CachedStep.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2

set_option maxRecDepth 32768 in
theorem emitted_validBody : validBody = validBody.take 45 ++ (validBody.drop 45).take 49 ++
    (validBody.drop 94).take 34 ++ validBody.drop 128 := rfl

theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr cachePtr : UInt64) (weights cache : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hValid : Valid weights cache token position)
    (hResources : Resources heap position cache.size (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : State (parameters weightsPtr cachePtr weights cache token position) frame)
    (Q : Assertion Unit)
    (hNext : ∀ final result,
      LogitsState (parameters weightsPtr cachePtr weights cache token position)
        (hiddenNode heap position).root (normalizedNode heap position cache.size).root
        (cacheNode heap position cache.size).root (logitsNode heap position cache.size).root (cache.size + 73728) result →
      (finalHeap heap position cache.size).At final →
      (finalHeap heap position cache.size).OwnsPacked final (cacheNode heap position cache.size)
        (cachedStep weights cache token position).cache →
      (finalHeap heap position cache.size).OwnsPacked final (logitsNode heap position cache.size)
        (cachedStep weights cache token position).logits →
      heap.Frame initial (finalHeap heap position cache.size) final →
      regionsDisjoint (cacheNode heap position cache.size).region (logitsNode heap position cache.size).region →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      Q (.Fallthrough final result)) : wp «module» validBody Q initial frame env := by
  have hNormSize : (finalNormOffset + 1536) * 4 ≤ weights.size := by rw [hValid.1]; rfl
  have hVocabSize : 50257 * 768 * 4 ≤ weights.size := by rw [hValid.1]; decide
  rw [emitted_validBody]
  simp only [List.append_assoc]
  apply hidden_spec env initial heap weightsPtr cachePtr weights cache token position frame hHeap hWeights hCache
    hWeightsProtected hCacheProtected hValid hResources.hidden hPages hState
  intro hiddenStore hiddenFrame hHiddenState hHiddenHeap hHidden hOutputCache hHiddenFrame hHiddenFresh hCacheFresh hHiddenCache hHiddenPages hHiddenCapacity
  have hNormResources : LayerNorm.Resources (hiddenHeap heap position cache.size) 1 (hiddenStore.memoryCap «module» 0) := by
    rw [hHiddenCapacity]; exact hResources.normalization
  have hNormFresh := LayerNorm.outputNode_fresh hNormResources
  apply normalized_spec env hiddenStore (hiddenHeap heap position cache.size) weightsPtr cachePtr
    (hiddenNode heap position).root (cacheNode heap position cache.size).root weights cache
    (cachedHidden weights cache token position).hidden token position (cache.size + 73728) hiddenFrame
    hHiddenHeap (hHiddenFrame.packed hWeightsProtected hWeights) hHidden.buffer.values
    (hHiddenFrame.protects _ _ hWeightsProtected) hHidden.payload_protects
    (CachedHidden.Spec.cachedHidden_hidden_size ..) hNormSize hNormResources hHiddenPages hHiddenState
  intro normStore normFrame hNormState hNormHeap hNorm hNormFrame hNormPages hNormCapacity
  have hCombinedFrame := hHiddenFrame.trans hNormFrame
  have hCurrentHidden := hNormFrame.ownsPacked hNormHeap hHidden
  have hCurrentCache := hNormFrame.ownsPacked hNormHeap hOutputCache
  have hNormHidden := hNormFresh.owns_disjoint hNorm.buffer.rootBound hHidden
  have hNormCache := hNormFresh.owns_disjoint hNorm.buffer.rootBound hOutputCache
  have hLogitsResources : LayerNorm.AllocationFits (normalizedHeap heap position cache.size) Vocabulary.outputNeed
      (normStore.memoryCap «module» 0) := by
    rw [hNormCapacity, hHiddenCapacity]; exact hResources.logits
  have hLogitsFresh := (normalizedHeap heap position cache.size).freshNode_allocated Vocabulary.outputNeed
    (fun h => (hLogitsResources h).1.le)
  apply logits_spec env normStore (normalizedHeap heap position cache.size) weightsPtr cachePtr
    (hiddenNode heap position).root (cacheNode heap position cache.size).root (normalizedNode heap position cache.size).root
    weights cache (normalized weights cache token position) token position (cache.size + 73728) normFrame
    hNormHeap (hCombinedFrame.packed hWeightsProtected hWeights) hNorm.buffer.values
    (hCombinedFrame.protects _ _ hWeightsProtected) hNorm.payload_protects
    (normalized_size ..) hVocabSize hLogitsResources hNormPages hNormState
  intro logitsStore logitsFrame hLogitsState hLogitsOutput
  have hLogitsHidden := hLogitsFresh.owns_disjoint hLogitsOutput.owned.buffer.rootBound hCurrentHidden
  have hLogitsCache := hLogitsFresh.owns_disjoint hLogitsOutput.owned.buffer.rootBound hCurrentCache
  have hLogitsNorm := hLogitsFresh.owns_disjoint hLogitsOutput.owned.buffer.rootBound hNorm
  have hFinalFrame := hCombinedFrame.trans hLogitsOutput.frame
  have hCapacity := (hLogitsOutput.memoryCap «module» 0).trans (hNormCapacity.trans hHiddenCapacity)
  have hState' : LogitsState (parameters weightsPtr cachePtr weights cache token position)
      (hiddenNode heap position).root (normalizedNode heap position cache.size).root
      (cacheNode heap position cache.size).root (logitsNode heap position cache.size).root
      (cachedHidden weights cache token position).cache.size logitsFrame := by
    simpa only [CachedHidden.Spec.cachedHidden_cache_size, logitsNode, allocatedNode] using hLogitsState
  have hCleanup := cleanup_spec env logitsStore initial (logitsHeap heap position cache.size) heap _
    (hiddenNode heap position) (normalizedNode heap position cache.size) (cacheNode heap position cache.size) (logitsNode heap position cache.size)
    (cachedHidden weights cache token position).hidden (normalized weights cache token position)
    (cachedHidden weights cache token position).cache (vocabularyHead weights (normalized weights cache token position))
    logitsFrame hLogitsOutput.heapAt
    (hLogitsOutput.frame.ownsPacked hLogitsOutput.heapAt hCurrentHidden)
    (hLogitsOutput.frame.ownsPacked hLogitsOutput.heapAt hNorm)
    (hLogitsOutput.frame.ownsPacked hLogitsOutput.heapAt hCurrentCache) hLogitsOutput.owned
    hNormHidden hHiddenCache hNormCache (regionsDisjoint_symm hLogitsHidden) (regionsDisjoint_symm hLogitsNorm)
    hFinalFrame hHiddenFresh (hHiddenFrame.freshNode hNormFresh) rfl hState' Q []
  simp only [List.append_nil] at hCleanup
  apply hCleanup
  intro hFinalHeap hFinalCache hFinalLogits hFinalFrame
  simp only [wp_nil]
  apply hNext _ logitsFrame hLogitsState hFinalHeap
  · simpa only [cachedStep_valid hValid, finalHeap] using hFinalCache
  · simpa only [cachedStep_valid hValid, finalHeap] using hFinalLogits
  · exact hFinalFrame
  · exact regionsDisjoint_symm hLogitsCache
  · exact hLogitsOutput.pages
  · exact hCapacity

#print axioms body_spec

end Project.Gpt2CachedStep.Entry
