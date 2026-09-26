import Project.Gpt2QuantizedCached.Entry.FrontPlan

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

theorem cacheBody_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
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
      let output := cacheResult weights cache token position
      ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status (outputCacheNode heap weights cache token position))
        (statusRoot output.status (outputLogitsNode heap weights cache token position))
        output.cache.size output.logits.size result →
      Completion heap initial (cacheHeap heap weights cache token position) final output.status
        (outputCacheNode heap weights cache token position) (outputLogitsNode heap weights cache token position)
        output.cache output.logits → wp «module» rest Q final result env) :
    wp «module» (cacheBody ++ rest) Q initial frame env := by
  rw [emitted_cache]
  apply gate_spec env initial heap (acceptedHeap heap weights cache token position)
    (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
    (outputCacheNode heap weights cache token position) (outputLogitsNode heap weights cache token position)
    (hiddenStageResult weights (cachedHidden weights cache token position) position)
    cacheTestCode acceptedBody (!finiteWords cache 0 (position * cachePositionWords)) 3 frame
    hHeap hPages (by rfl) (by decide)
  · intro R tail hContinue
    apply cacheTest_spec env initial weightsOwner weightsPtr cacheOwner cachePtr weights cache token position frame
      hCache hInput hState
    intro checked hParams hLength hTyped hValues
    exact hContinue checked ⟨hParams.trans hState.paramsEq, hLength, rfl, hTyped⟩ hValues
  · intro _ prepared hPrepared R hContinue
    rw [← List.append_nil acceptedBody]
    apply accepted_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr weights cache token position prepared
      hHeap hWeights hCache hWeightsProtected hCacheProtected hHeader hInput hResources hPages hPrepared
    intro final result
    dsimp only
    intro hResult hMemory
    simpa only [wp_nil] using hContinue final result hResult hMemory
  · exact hNext

#print axioms cacheBody_spec
end Project.Gpt2QuantizedCached.Entry
