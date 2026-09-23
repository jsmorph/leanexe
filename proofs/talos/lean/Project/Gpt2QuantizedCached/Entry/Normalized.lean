import Project.Gpt2QuantizedCached.Entry.Hidden
import Project.Gpt2QuantizedCached.LayerNorm

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def normalizedCode : Program :=
  [.localGet 0,
   .localSet 38,
   .localGet 1,
   .localSet 39,
   .localGet 2,
   .localSet 40,
   .localGet 32,
   .localSet 41,
   .localGet 33,
   .localSet 42,
   .localGet 34,
   .localSet 43,
   .call 20,
   .localSet 96,
   .constI64 4,
   .localSet 97,
   .localGet 97,
   .constI64 0,
   .eqI64,
   .iff 0 1 [
       .constI64 0
      ] [
       .localGet 96,
       .localGet 97,
       .divUI64
      ] [] [.i64],
   .localSet 44,
   .call 20,
   .localSet 99,
   .constI64 4,
   .localSet 100,
   .localGet 100,
   .constI64 0,
   .eqI64,
   .iff 0 1 [
       .constI64 0
      ] [
       .localGet 99,
       .localGet 100,
       .divUI64
      ] [] [.i64],
   .localSet 96,
   .constI64 768,
   .localSet 97,
   .localGet 96,
   .localGet 97,
   .addI64,
   .localTee 98,
   .localGet 96,
   .ltUI64,
   .iff 0 1 [
       .unreachable
      ] [
       .localGet 98
      ] [] [.i64],
   .localSet 45,
   .constI64 1,
   .localSet 46,
   .localGet 38,
   .localGet 39,
   .localGet 40,
   .localGet 41,
   .localGet 42,
   .localGet 43,
   .localGet 44,
   .localGet 45,
   .localGet 46,
   .call 34,
   .localSet 49,
   .localSet 48,
   .localSet 47,
   .localGet 47,
   .localSet 50,
   .localGet 48,
   .localSet 51,
   .localGet 49,
   .localSet 52]

theorem emitted_normalized : hiddenBody.take 61 = normalizedCode := rfl

structure NormalizedState (params : List Value) (hidden cache normalized : UInt64)
    (cacheSize : Nat) (frame : Locals) : Prop
    extends HiddenState params 0 hidden cache 3072 cacheSize frame where
  releaseNormalized : frame.locals[39]? = some (.i64 normalized)
  normalizedOwner : frame.locals[42]? = some (.i64 normalized)
  normalizedPtr : frame.locals[43]? = some (.i64 normalized)
  normalizedSize : frame.locals[44]? = some (.i64 3072)

theorem normalized_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr hiddenPtr outputCachePtr : UInt64)
    (weights cache hidden : ByteArray) (token : UInt32) (position outputCacheSize : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hHidden : ByteArrayAt initial.mem hiddenPtr.toNat hidden)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hHiddenProtected : heap.Protects hiddenPtr.toNat (hiddenPtr.toNat + hidden.size))
    (hHeader : validHeader weights = true) (hHiddenSize : hidden.size = 3072)
    (hResources : Gpt2CachedStep.LayerNorm.Resources heap 1 (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : HiddenState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      0 hiddenPtr outputCachePtr 3072 outputCacheSize frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      NormalizedState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        hiddenPtr outputCachePtr (Gpt2CachedStep.LayerNorm.outputNode heap 1).root outputCacheSize result →
      (Gpt2CachedStep.LayerNorm.finalHeap heap 1).At final →
      (Gpt2CachedStep.LayerNorm.finalHeap heap 1).OwnsPacked final (Gpt2CachedStep.LayerNorm.outputNode heap 1)
        (LeanExe.Models.Gpt2.layerNorm weights hidden (finalNormOffset / 4) (finalNormOffset / 4 + 768) 1) →
      heap.Frame initial (Gpt2CachedStep.LayerNorm.finalHeap heap 1) final →
      final.mem.pages ≤ 65536 → final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0 →
      wp «module» rest Q final result env) :
    wp «module» (normalizedCode ++ rest) Q initial frame env := by
  have hWeightsSize := Model.size_of_header weights hHeader
  have hScale : (finalNormOffset / 4 + 768) * 4 ≤ weights.size := by rw [hWeightsSize]; decide
  have hBias : (finalNormOffset / 4 + 768 + 768) * 4 ≤ weights.size := by rw [hWeightsSize]; decide
  have hCall := LayerNorm.layerNorm_exact env initial heap weightsOwner hiddenPtr weightsPtr hiddenPtr weights hidden
    (finalNormOffset / 4) (finalNormOffset / 4 + 768) 1 hHeap hWeights hHidden hWeightsProtected hHiddenProtected
    (by rw [hHiddenSize]) hScale hBias hResources hPages
  have hFour : (4 : UInt64) ≠ 0 := by decide
  have hDiv : UInt64.ofNat finalNormOffset / 4 = UInt64.ofNat (finalNormOffset / 4) := rfl
  simp only [hHiddenSize] at hCall
  simp only [normalizedCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hState.values,
    hState.hiddenOwner, hState.hiddenPtr, hState.hiddenSize]
  refine wp_call_tw (Layout.finalNormOffset_exact env initial) ?_
  rintro final returned ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hFour, hDiv]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hFour, hDiv]
  refine wp_call_tw (Layout.finalNormOffset_exact env initial) ?_
  rintro final returned ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hFour, hDiv]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hFour, hDiv]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hFour, hDiv]
  refine wp_call_tw hCall ?_
  rintro final returned ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  rw [Gpt2CachedStep.LayerNorm.layerNorm_size] at hReturned
  subst returned
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hFour, hDiv]
  apply hNext
  · constructor
    · constructor
      · constructor <;> simp (config := { maxDischargeDepth := 64 }) only [parameters, CachedHidden.parameters,
          hState.length, List.length_set, I64Values.set, hState.typed]
      all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
        Nat.reduceLT, reduceIte, hState.releaseHidden, hState.releaseCache, hState.status, hState.hiddenOwner, hState.hiddenPtr,
        hState.hiddenSize, hState.cacheOwner, hState.cachePtr, hState.cacheSize]
    all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
      Nat.reduceLT, reduceIte, show UInt64.ofNat (4 * (1 * 768)) = 3072 from rfl]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms normalized_spec
end Project.Gpt2QuantizedCached.Entry
