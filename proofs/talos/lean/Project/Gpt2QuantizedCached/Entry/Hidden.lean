import Project.Gpt2QuantizedCached.Entry.Code

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem hidden_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hHeader : validHeader weights = true) (hInput : invalidInput cache token position = false)
    (hResources : CachedHidden.Resources heap weights cache token position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : State (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let output := cachedHidden weights cache token position
      HiddenState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status (CachedHidden.traversed heap weights cache token position).hidden)
        (statusRoot output.status (CachedHidden.cacheNode heap weights cache token position))
        output.hidden.size output.cache.size result →
      CachedHidden.Completion heap initial (CachedHidden.finalHeap heap weights cache token position) final output.status
        (CachedHidden.traversed heap weights cache token position).hidden (CachedHidden.cacheNode heap weights cache token position)
        output.hidden output.cache → wp «module» rest Q final result env) :
    wp «module» (hiddenCode ++ rest) Q initial frame env := by
  have hValid := (invalidInput_false cache token position).mp hInput
  rcases valid_extents weights cache token position hHeader hInput with
    ⟨hScale, hToken, hPosition, hBlocks, _, hCacheSize, hAppend⟩
  simp only [hiddenCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hState.values]
  refine wp_call_tw (CachedHidden.Spec.cachedHidden_exact env initial heap weightsOwner weightsPtr cacheOwner cachePtr
    weights cache token position hHeap hWeights hCache hWeightsProtected hCacheProtected hValid.1 hValid.2.1
    hScale hToken hPosition hBlocks hCacheSize hAppend hResources hPages) ?_
  rintro final returned ⟨hReturned, hCompletion⟩
  rw [CachedHidden.resultValues] at hReturned
  subst returned
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length]
  apply hNext
  · constructor
    · constructor <;>
        simp (config := { maxDischargeDepth := 64 }) only [parameters, CachedHidden.parameters, hState.length, List.length_set,
          I64Values.set, hState.typed]
    all_goals simp only [hState.length, List.length_set, List.getElem?_set,
      Nat.reduceEqDiff, Nat.reduceLT, reduceIte]
  · exact hCompletion

#print axioms hidden_spec
end Project.Gpt2QuantizedCached.Entry
