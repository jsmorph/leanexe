import Project.Gpt2CachedStep.Entry.Code
import Project.Gpt2CachedStep.Layout

namespace Project.Gpt2CachedStep.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def normalizedCode : Wasm.Program :=
  [.constI64 0, .localSet 26, .localGet 0, .localSet 27, .localGet 1, .localSet 28,
   .localGet 20, .localSet 29, .localGet 21, .localSet 30, .localGet 22, .localSet 31,
   .call 14, .localSet 32, .localGet 32, .localSet 33,
   .call 14, .localSet 57, .constI64 768, .localSet 58,
   .localGet 57, .localGet 58, .addI64, .localTee 59, .localGet 57, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 59] [] [.i64], .localSet 34,
   .constI64 1, .localSet 35,
   .localGet 26, .localGet 27, .localGet 28, .localGet 29, .localGet 30, .localGet 31,
   .localGet 33, .localGet 34, .localGet 35, .call 20,
   .localSet 38, .localSet 37, .localSet 36,
   .localGet 36, .localSet 39, .localGet 37, .localSet 40, .localGet 38, .localSet 41]

set_option maxRecDepth 32768 in
theorem emitted_normalized : (validBody.drop 45).take 49 = normalizedCode := rfl

theorem normalized_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr cachePtr hiddenPtr outputCachePtr : UInt64) (weights cache input : ByteArray)
    (token : UInt32) (position cacheSize : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem hiddenPtr.toNat input)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects hiddenPtr.toNat (hiddenPtr.toNat + input.size))
    (hInputSize : input.size = 3072) (hWeightsSize : (finalNormOffset + 1536) * 4 ≤ weights.size)
    (hResources : LayerNorm.Resources heap 1 (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : HiddenState (parameters weightsPtr cachePtr weights cache token position) hiddenPtr outputCachePtr cacheSize frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      NormalizedState (parameters weightsPtr cachePtr weights cache token position)
        hiddenPtr outputCachePtr (LayerNorm.outputNode heap 1).root cacheSize result →
      (LayerNorm.finalHeap heap 1).At final →
      (LayerNorm.finalHeap heap 1).OwnsPacked final (LayerNorm.outputNode heap 1)
        (layerNorm weights input finalNormOffset (finalNormOffset + 768) 1) →
      heap.Frame initial (LayerNorm.finalHeap heap 1) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((validBody.drop 45).take 49 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hValues, hTyped⟩, hHidden14, hHidden20, hHidden21, hHidden22, hCache23, hCache24, hCache25, hCache17, hEmpty6, hEmpty9⟩
  have hScaleSize : (finalNormOffset + 768) * 4 ≤ weights.size := by
    exact (Nat.mul_le_mul_right 4 (Nat.add_le_add_left (by decide : 768 ≤ 1536) finalNormOffset)).trans hWeightsSize
  have hBiasSize : (finalNormOffset + 768 + 768) * 4 ≤ weights.size := by
    rw [Nat.add_assoc]; exact hWeightsSize
  have hAdd : UInt64.ofNat finalNormOffset + 768 = UInt64.ofNat (finalNormOffset + 768) := by simp
  have hCall := LayerNorm.Spec.layerNorm_exact env initial heap 0 hiddenPtr weightsPtr hiddenPtr weights input
    finalNormOffset (finalNormOffset + 768) 1 hHeap hWeights hInput hWeightsProtected hInputProtected
    (by rw [hInputSize]) hScaleSize hBiasSize hResources hPages
  simp only [hInputSize] at hCall
  rw [emitted_normalized]
  simp only [normalizedCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hHidden20, hHidden21, hHidden22]
  refine wp_call_tw (Layout.finalNormOffset_exact env initial) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_call_tw (Layout.finalNormOffset_exact env final) ?_
  rintro final' values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, parameters, hLocals, hAdd]
  refine wp_call_tw hCall ?_
  rintro final'' values ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  rw [LayerNorm.layerNorm_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [NormalizedState, HiddenState, State, parameters, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, hHidden14, hHidden20, hHidden21, hHidden22, hCache23, hCache24, hCache25, hCache17, hEmpty6, hEmpty9,
      show UInt64.ofNat (4 * (1 * 768)) = 3072 from rfl, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms normalized_spec

end Project.Gpt2CachedStep.Entry
