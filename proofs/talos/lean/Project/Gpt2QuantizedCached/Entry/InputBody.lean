import Project.Gpt2QuantizedCached.Entry.CacheBody

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

theorem inputBody_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hHeader : validHeader weights = true)
    (hCacheFit : cache.size < UInt64.size) (hPositionFit : position < UInt64.size)
    (hResources : invalidInput cache token position = false →
      Resources heap weights cache token position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : State (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let output := inputResult weights cache token position
      ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status (outputCacheNode heap weights cache token position))
        (statusRoot output.status (outputLogitsNode heap weights cache token position))
        output.cache.size output.logits.size result →
      Completion heap initial (inputHeap heap weights cache token position) final output.status
        (outputCacheNode heap weights cache token position) (outputLogitsNode heap weights cache token position)
        output.cache output.logits → wp «module» rest Q final result env) :
    wp «module» (inputBody ++ rest) Q initial frame env := by
  rw [emitted_input]
  apply gate_spec env initial heap (cacheHeap heap weights cache token position)
    (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
    (outputCacheNode heap weights cache token position) (outputLogitsNode heap weights cache token position)
    (cacheResult weights cache token position)
    (inputTestCode ++ ReadOnlyDisjunction.canonicalProgram) cacheBody (invalidInput cache token position) 3 frame
    hHeap hPages (by rfl) (by decide)
  · intro R tail hContinue
    rw [List.append_assoc]
    apply inputTest_spec env initial weightsOwner weightsPtr cacheOwner cachePtr weights cache token position frame
      hCacheFit hPositionFit hState
    intro checked hParams hLength hTyped hValues
    apply ReadOnlyDisjunction.canonical_spec _ _ _ _ _ hValues
    exact hContinue checked ⟨hParams.trans hState.paramsEq, hLength, rfl, hTyped⟩ hValues
  · intro hInput prepared hPrepared R hContinue
    rw [← List.append_nil cacheBody]
    apply cacheBody_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr weights cache token position prepared
      hHeap hWeights hCache hWeightsProtected hCacheProtected hHeader hInput (hResources hInput) hPages hPrepared
    intro final result
    dsimp only
    intro hResult hMemory
    simpa only [wp_nil] using hContinue final result hResult hMemory
  · exact hNext

#print axioms inputBody_spec
end Project.Gpt2QuantizedCached.Entry
