import Project.Gpt2QuantizedCached.Entry.Plan

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

set_option maxRecDepth 32768 in
theorem acceptedBody_parts : acceptedBody = hiddenCode ++ hiddenStageCode := rfl

theorem accepted_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hHeader : validHeader weights = true) (hInput : invalidInput cache token position = false)
    (hResources : Resources heap weights cache token position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : State (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let output := hiddenStageResult weights (cachedHidden weights cache token position) position
      ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status (outputCacheNode heap weights cache token position))
        (statusRoot output.status (outputLogitsNode heap weights cache token position))
        output.cache.size output.logits.size result →
      Completion heap initial (acceptedHeap heap weights cache token position) final output.status
        (outputCacheNode heap weights cache token position) (outputLogitsNode heap weights cache token position)
        output.cache output.logits → wp «module» rest Q final result env) :
    wp «module» (acceptedBody ++ rest) Q initial frame env := by
  rw [acceptedBody_parts, List.append_assoc]
  apply hidden_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr weights cache token position frame
    hHeap hWeights hCache hWeightsProtected hCacheProtected hHeader hInput hResources.hidden hPages hState
  intro hidden prepared
  dsimp only
  intro hPrepared hMemory
  have hValid := (invalidInput_false cache token position).mp hInput
  have hSizes := CachedHidden.cachedHidden_sizes weights cache token position
  have hNormResources : Gpt2CachedStep.LayerNorm.Resources
      (CachedHidden.finalHeap heap weights cache token position) 1 (hidden.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    change Gpt2CachedStep.LayerNorm.Resources _ _ (hidden.memoryCap «module» 0)
    rw [hMemory.capacity]
    exact hResources.normalized
  have hProjectionResources : GroupedProjection.Projection.Resources
      (normalizationHeap (CachedHidden.finalHeap heap weights cache token position)) 768 50257 1 (hidden.memoryCap «module» 0) := by
    rw [hMemory.capacity]
    exact hResources.logits
  apply hiddenStage_spec env initial hidden heap (CachedHidden.finalHeap heap weights cache token position)
    weightsOwner weightsPtr cacheOwner cachePtr (CachedHidden.traversed heap weights cache token position).hidden
    (outputCacheNode heap weights cache token position) weights cache (cachedHidden weights cache token position)
    token position prepared (hMemory.frame.packed hWeightsProtected hWeights)
    (hMemory.frame.protects _ _ hWeightsProtected) hMemory hHeader hValid.2.1
    (fun hZero => (hiddenSizes_success cache.size _ hSizes hZero).1)
    (fun hZero => by
      rw [(hiddenSizes_success cache.size _ hSizes hZero).2, hValid.2.2]
      simp only [cachePositionWords]
      omega) hNormResources hProjectionResources hPrepared
  exact hNext

#print axioms accepted_spec
end Project.Gpt2QuantizedCached.Entry
