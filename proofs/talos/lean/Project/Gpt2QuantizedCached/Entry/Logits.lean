import Project.Gpt2QuantizedCached.Entry.Normalized
import Project.Gpt2QuantizedCached.GroupedProjection.Budget

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def logitsCode : Program :=
  [.localGet 0,
   .localSet 58,
   .localGet 1,
   .localSet 59,
   .localGet 2,
   .localSet 60,
   .localGet 50,
   .localSet 61,
   .localGet 51,
   .localSet 62,
   .localGet 52,
   .localSet 63,
   .call 1,
   .localSet 64,
   .localGet 64,
   .localSet 65,
   .call 2,
   .localSet 66,
   .localGet 66,
   .localSet 67,
   .constI64 0,
   .localSet 68,
   .constI64 768,
   .localSet 69,
   .constI64 50257,
   .localSet 70,
   .constI64 1,
   .localSet 71,
   .constI64 0,
   .localSet 72,
   .localGet 58,
   .localGet 59,
   .localGet 60,
   .localGet 61,
   .localGet 62,
   .localGet 63,
   .localGet 65,
   .localGet 67,
   .localGet 68,
   .localGet 69,
   .localGet 70,
   .localGet 71,
   .localGet 72,
   .call 42,
   .localSet 75,
   .localSet 74,
   .localSet 73,
   .localGet 73,
   .localSet 76,
   .localGet 74,
   .localSet 77,
   .localGet 75,
   .localSet 78]

theorem emitted_logits : normalizedBody.take 53 = logitsCode := rfl

structure LogitsState (params : List Value) (hidden cache normalized logits : UInt64)
    (cacheSize : Nat) (frame : Locals) : Prop
    extends NormalizedState params hidden cache normalized cacheSize frame where
  releaseLogits : frame.locals[65]? = some (.i64 logits)
  logitsOwner : frame.locals[68]? = some (.i64 logits)
  logitsPtr : frame.locals[69]? = some (.i64 logits)
  logitsSize : frame.locals[70]? = some (.i64 201028)

theorem logits_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr hiddenPtr outputCachePtr normalizedPtr : UInt64)
    (weights cache normalized : ByteArray) (token : UInt32) (position outputCacheSize : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hNormalized : ByteArrayAt initial.mem normalizedPtr.toNat normalized)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hNormalizedProtected : heap.Protects normalizedPtr.toNat (normalizedPtr.toNat + normalized.size))
    (hHeader : validHeader weights = true) (hNormalizedSize : normalized.size = 3072)
    (hResources : GroupedProjection.Projection.Resources heap 768 50257 1 (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : NormalizedState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      hiddenPtr outputCachePtr normalizedPtr outputCacheSize frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      LogitsState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        hiddenPtr outputCachePtr normalizedPtr (GroupedProjection.Projection.outputNode heap 768 50257 1).root
        outputCacheSize result →
      GroupedProjection.Projection.Output heap initial final weights normalized tokenWeightOffset tokenScaleOffset
        0 768 50257 1 false → wp «module» rest Q final result env) :
    wp «module» (logitsCode ++ rest) Q initial frame env := by
  have hWeightsSize := Model.size_of_header weights hHeader
  have hMatrix : tokenWeightOffset + 768 * 50257 ≤ weights.size := by rw [hWeightsSize]; decide
  have hScales : tokenScaleOffset + 50257 * 4 ≤ weights.size := by rw [hWeightsSize]; decide
  have hCall := GroupedProjection.Spec.linearGroupedRows_exact env initial heap
    weightsOwner weightsPtr normalizedPtr normalizedPtr weights normalized tokenWeightOffset tokenScaleOffset 0
    768 50257 1 false hHeap hWeights hNormalized hMatrix hScales (by intro h; contradiction)
    (by rw [hNormalizedSize]) (by decide) (by decide) (by decide) hWeightsProtected hNormalizedProtected
    (by decide) (by decide) hResources.scales hResources.values hResources.output hPages
  simp only [hNormalizedSize, GroupedProjection.Projection.parameters, List.reverse_cons,
    List.reverse_nil, List.cons_append, List.nil_append] at hCall
  simp only [logitsCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hState.values,
    hState.normalizedOwner, hState.normalizedPtr, hState.normalizedSize]
  refine wp_call_tw (Layout.tokenWeightOffset_exact env initial) ?_
  rintro final returned ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length]
  refine wp_call_tw (Layout.tokenScaleOffset_exact env initial) ?_
  rintro final returned ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length]
  refine wp_call_tw hCall ?_
  rintro final returned ⟨rfl, hOutput⟩
  wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length]
  apply hNext _ _ ?_ hOutput
  constructor
  · constructor
    · constructor
      · constructor <;> simp (config := { maxDischargeDepth := 64 }) only [parameters, CachedHidden.parameters,
          hState.length, List.length_set, I64Values.set, hState.typed]
      all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
        Nat.reduceLT, reduceIte, hState.releaseHidden, hState.releaseCache, hState.status, hState.hiddenOwner, hState.hiddenPtr,
        hState.hiddenSize, hState.cacheOwner, hState.cachePtr, hState.cacheSize]
    all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
      Nat.reduceLT, reduceIte, hState.releaseNormalized, hState.normalizedOwner, hState.normalizedPtr, hState.normalizedSize]
  all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
    Nat.reduceLT, reduceIte, show UInt64.ofNat (4 * (1 * 50257)) = 201028 from rfl]

#print axioms logits_spec
end Project.Gpt2QuantizedCached.Entry
