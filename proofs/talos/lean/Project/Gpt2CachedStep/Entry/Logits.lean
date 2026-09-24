import Project.Gpt2CachedStep.Entry.Code

namespace Project.Gpt2CachedStep.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def logitsCode : Wasm.Program :=
  [.localGet 23, .localSet 51, .localGet 24, .localSet 52, .localGet 25, .localSet 53,
   .constI64 0, .localSet 42, .localGet 0, .localSet 43, .localGet 1, .localSet 44,
   .localGet 39, .localSet 45, .localGet 40, .localSet 46, .localGet 41, .localSet 47,
   .localGet 42, .localGet 43, .localGet 44, .localGet 45, .localGet 46, .localGet 47, .call 37,
   .localSet 50, .localSet 49, .localSet 48,
   .localGet 48, .localSet 54, .localGet 49, .localSet 55, .localGet 50, .localSet 56]

set_option maxRecDepth 32768 in
theorem emitted_logits : (validBody.drop 94).take 34 = logitsCode := rfl

theorem logits_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr cachePtr hiddenPtr outputCachePtr normalizedPtr : UInt64) (weights cache input : ByteArray)
    (token : UInt32) (position cacheSize : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem normalizedPtr.toNat input)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects normalizedPtr.toNat (normalizedPtr.toNat + input.size))
    (hInputSize : input.size = 3072) (hWeightsSize : 50257 * 768 * 4 ≤ weights.size)
    (hResources : LayerNorm.AllocationFits heap Vocabulary.outputNeed (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : NormalizedState (parameters weightsPtr cachePtr weights cache token position)
      hiddenPtr outputCachePtr normalizedPtr cacheSize frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      LogitsState (parameters weightsPtr cachePtr weights cache token position)
        hiddenPtr normalizedPtr outputCachePtr (allocatedRoot heap.top Vocabulary.outputNeed heap.nodes) cacheSize result →
      heap.PackedOutput initial final Vocabulary.outputNeed (vocabularyHead weights input) →
      wp «module» rest Q final result env) :
    wp «module» ((validBody.drop 94).take 34 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨⟨hParams, hLocals, hValues, hTyped⟩, hHidden14, hHidden20, _, _, hCache23, hCache24, hCache25, hCache17, hEmpty6, hEmpty9⟩,
    hNorm36, hNorm39, hNorm40, hNorm41⟩
  have hCall := Vocabulary.Spec.vocabularyHead_exact env initial heap 0 normalizedPtr weightsPtr normalizedPtr weights input
    hHeap hWeights hInput hWeightsSize (by rw [hInputSize]) hWeightsProtected hInputProtected hResources hPages
  simp only [hInputSize] at hCall
  rw [emitted_logits]
  simp only [logitsCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hCache23, hCache24, hCache25, hNorm39, hNorm40, hNorm41]
  refine wp_call_tw hCall ?_
  rintro final values ⟨hReturned, hOutput⟩
  rw [Vocabulary.vocabularyHead_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [LogitsState, State, parameters, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, hHidden14, hHidden20, hCache23, hCache17, hEmpty6, hEmpty9, hNorm36, show UInt64.ofNat 201028 = 201028 from rfl, and_self]
  · exact hOutput

#print axioms logits_spec

end Project.Gpt2CachedStep.Entry
