import Project.Gpt2QuantizedCached.Entry.HiddenFailure

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def hiddenStageResult (weights : ByteArray) (hidden : HiddenResult) (position : Nat) : CachedResult :=
  if hidden.status = 0 then normalizedResult weights hidden.cache (normalizedBytes weights hidden.hidden) position
  else ⟨hidden.status, .empty, .empty⟩

def hiddenStageHeap (heap : Heap) (hiddenNode cacheNode : FreeNode)
    (weights : ByteArray) (hidden : HiddenResult) (position : Nat) : Heap :=
  if hidden.status = 0 then
    (normalizedStageHeap heap cacheNode weights hidden.hidden hidden.cache position).release hiddenNode
  else heap

def hiddenStageCode : Program := CachedHidden.failureTestCode 31 ++
  [.iff 0 0 hiddenFailureCode hiddenBody] ++ releaseCode 25

set_option maxRecDepth 32768 in
theorem emitted_hiddenStage : acceptedBody.drop 46 = hiddenStageCode := rfl

theorem hiddenStage_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (hiddenNode cacheNode : FreeNode)
    (weights cache : ByteArray) (hidden : HiddenResult) (token : UInt32) (position : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hMemory : CachedHidden.Completion before original heap initial hidden.status hiddenNode cacheNode hidden.hidden hidden.cache)
    (hHeader : validHeader weights = true) (hPosition : position < 128)
    (hHiddenSize : hidden.status = 0 → hidden.hidden.size = 3072)
    (hCacheSize : hidden.status = 0 → (position + 1) * cachePositionWords * 4 ≤ hidden.cache.size)
    (hNormResources : Gpt2CachedStep.LayerNorm.Resources heap 1 (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hProjectionResources : GroupedProjection.Projection.Resources (normalizationHeap heap) 768 50257 1
      (initial.memoryCap «module» 0))
    (hState : HiddenState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      hidden.status (statusRoot hidden.status hiddenNode) (statusRoot hidden.status cacheNode)
      hidden.hidden.size hidden.cache.size frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let output := hiddenStageResult weights hidden position
      ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status cacheNode) (statusRoot output.status (vocabularyNode (normalizationHeap heap)))
        output.cache.size output.logits.size result →
      Completion before original (hiddenStageHeap heap hiddenNode cacheNode weights hidden position)
        final output.status cacheNode (vocabularyNode (normalizationHeap heap)) output.cache output.logits →
      wp «module» rest Q final result env) :
    wp «module» (hiddenStageCode ++ rest) Q initial frame env := by
  simp only [hiddenStageCode, List.append_assoc]
  apply CachedHidden.failureGuard_spec env initial frame 31 hidden.status hState.values
    (hState.toState.get_local (by rfl) 23 _ (by decide) hState.status)
  by_cases hZero : hidden.status = 0
  · simp only [hZero, ite_true]
    rw [← List.append_nil hiddenBody]
    have hState' : HiddenState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        0 hiddenNode.root cacheNode.root 3072 hidden.cache.size frame := by
      simpa only [hZero, statusRoot, ite_true, hHiddenSize hZero] using hState
    apply normalizedStage_spec env original initial before heap weightsOwner weightsPtr cacheOwner cachePtr hiddenNode cacheNode
      weights cache hidden.hidden hidden.cache token position frame hMemory.heapAt hWeights hWeightsProtected
      (hMemory.hidden.owned hZero) (hMemory.cache.owned hZero) (hMemory.cacheFresh hZero) (hMemory.separated hZero)
      hMemory.frame hMemory.pages hMemory.capacity hHeader (hHiddenSize hZero) (hCacheSize hZero) hPosition
      hNormResources hProjectionResources hState'
    intro final result
    dsimp only
    intro hResult hRead hOutput hHiddenOwned hSep
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hRun : wp «module» (releaseCode 25 ++ rest) Q final result env := by
      apply releaseResult_spec env original final before _ _ _ cacheNode (vocabularyNode (normalizationHeap heap)) hiddenNode
        _ _ hidden.hidden result 25 hOutput hHiddenOwned (hMemory.hiddenFresh hZero)
        (fun _ => hMemory.separated hZero) hSep (by rfl) hResult
        (hResult.toState.get_local (by rfl) 17 _ (by decide) hRead)
      intro hReleased
      have hRun := hNext ((normalizedStageHeap heap cacheNode weights hidden.hidden hidden.cache position).releaseStore final hiddenNode) result
      simp only [hiddenStageResult, hiddenStageHeap, hZero, ite_true] at hRun
      exact hRun hResult hReleased
    simpa only [← hResult.values] using hRun
  · simp only [hZero, ite_false]
    rw [← List.append_nil hiddenFailureCode]
    have hState' : HiddenState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        hidden.status 0 0 0 0 frame := by
      simpa only [statusRoot, hZero, ite_false, hMemory.hidden.empty hZero, hMemory.cache.empty hZero,
        ByteArray.size_empty] using hState
    apply failureHidden_spec env initial _ hidden.status frame (by rfl) hState'
    intro result hResult hRead
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hRun : wp «module» (releaseCode 25 ++ rest) Q initial result env := by
      apply releaseNullResult_spec env initial _ hidden.status 25 result (by rfl) hResult
        (hResult.toState.get_local (by rfl) 17 _ (by decide) hRead)
      have hRun := hNext initial result
      simp only [hiddenStageResult, hiddenStageHeap, hZero, ite_false, statusRoot, ByteArray.size_empty] at hRun
      exact hRun hResult (Completion.failure before heap original initial hidden.status cacheNode
        (vocabularyNode (normalizationHeap heap)) hZero hMemory.heapAt hMemory.frame hMemory.pages hMemory.capacity)
    simpa only [← hResult.values] using hRun

#print axioms hiddenStage_spec
end Project.Gpt2QuantizedCached.Entry
