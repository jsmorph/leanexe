import Project.Gpt2QuantizedCached.Entry.InputBody

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

set_option maxRecDepth 32768 in
theorem entryFront_code : func59.take 22 = headerCode ++
    [.iff 0 0 (failureResultCode (.constI64 1)) inputBody] := rfl

theorem front_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hCacheFit : cache.size < UInt64.size) (hPositionFit : position < UInt64.size)
    (hResources : invalidInput cache token position = false →
      Resources heap weights cache token position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : State (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let output := cachedStep weights cache token position
      ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status (outputCacheNode heap weights cache token position))
        (statusRoot output.status (outputLogitsNode heap weights cache token position))
        output.cache.size output.logits.size result →
      Completion heap initial (finalHeap heap weights cache token position) final output.status
        (outputCacheNode heap weights cache token position) (outputLogitsNode heap weights cache token position)
        output.cache output.logits → wp «module» rest Q final result env) :
    wp «module» (func59.take 22 ++ rest) Q initial frame env := by
  have hCode : func59.take 22 = headerCode ++
      [.iff 0 0 (failureResultCode (.constI64 1)) inputBody] := by
    exact entryFront_code
  rw [hCode]
  have hNext' := hNext
  simp only [cachedStep_selected] at hNext'
  apply gate_spec env initial heap (inputHeap heap weights cache token position)
    (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
    (outputCacheNode heap weights cache token position) (outputLogitsNode heap weights cache token position)
    (inputResult weights cache token position) headerCode inputBody (!validHeader weights) 1 frame
    hHeap hPages (by rfl) (by decide)
  · intro R tail hContinue
    apply header_spec env initial weightsOwner weightsPtr cacheOwner cachePtr weights cache token position frame
      hWeights hState
    intro checked hParams hLength hTyped hValues
    exact hContinue checked ⟨hParams.trans hState.paramsEq, hLength, rfl, hTyped⟩ hValues
  · intro hHeader prepared hPrepared R hContinue
    have hHeader' : validHeader weights = true := by simpa using hHeader
    rw [← List.append_nil inputBody]
    apply inputBody_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr weights cache token position prepared
      hHeap hWeights hCache hWeightsProtected hCacheProtected hHeader' hCacheFit hPositionFit hResources hPages hPrepared
    intro final result
    dsimp only
    intro hResult hMemory
    simpa only [wp_nil] using hContinue final result hResult hMemory
  · exact hNext'

#print axioms front_spec
end Project.Gpt2QuantizedCached.Entry
