import Project.Gpt2QuantizedCached.CachedBlock.Structure
import Project.Gpt2QuantizedCached.CachedBlock.KernelState

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized GroupedProjection.Projection

def expandedCode : Wasm.Program := [
   .localGet 0,
   .localSet 121,
   .localGet 1,
   .localSet 122,
   .localGet 2,
   .localSet 123,
   .localGet 113,
   .localSet 124,
   .localGet 114,
   .localSet 125,
   .localGet 115,
   .localSet 126,
   .localGet 11,
   .localSet 196,
   .call 13,
   .localSet 197,
   .localGet 196,
   .localGet 197,
   .addI64,
   .localTee 198,
   .localGet 196,
   .ltUI64,
   .iff 0 1 [
    .unreachable
   ] [
    .localGet 198
   ] [] [.i64],
   .localSet 127,
   .localGet 11,
   .localSet 196,
   .call 14,
   .localSet 197,
   .localGet 196,
   .localGet 197,
   .addI64,
   .localTee 198,
   .localGet 196,
   .ltUI64,
   .iff 0 1 [
    .unreachable
   ] [
    .localGet 198
   ] [] [.i64],
   .localSet 128,
   .localGet 11,
   .localSet 196,
   .call 15,
   .localSet 197,
   .localGet 196,
   .localGet 197,
   .addI64,
   .localTee 198,
   .localGet 196,
   .ltUI64,
   .iff 0 1 [
    .unreachable
   ] [
    .localGet 198
   ] [] [.i64],
   .localSet 129,
   .constI64 768,
   .localSet 130,
   .constI64 3072,
   .localSet 131,
   .constI64 1,
   .localSet 132,
   .constI64 1,
   .localSet 133,
   .localGet 121,
   .localGet 122,
   .localGet 123,
   .localGet 124,
   .localGet 125,
   .localGet 126,
   .localGet 127,
   .localGet 128,
   .localGet 129,
   .localGet 130,
   .localGet 131,
   .localGet 132,
   .localGet 133,
   .call 42,
   .localSet 136,
   .localSet 135,
   .localSet 134,
   .localGet 134,
   .localSet 137,
   .localGet 135,
   .localSet 138,
   .localGet 136,
   .localSet 139
  ]

theorem emitted_expanded : normalized2Success.take 79 = expandedCode := rfl

theorem expanded_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr normalizedPtr : UInt64)
    (weights input cache normalized : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hNormalized : ByteArrayAt initial.mem normalizedPtr.toNat normalized)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hNormalizedProtected : heap.Protects normalizedPtr.toNat (normalizedPtr.toNat + normalized.size))
    (hNormalizedSize : normalized.size = 3072)
    (hExtent : base + blockBytes ≤ weights.size)
    (hResources : Resources heap 768 3072 1 (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 193) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (hCopiedOwner : frame.locals[102]? = some (.i64 normalizedPtr))
    (hCopiedPtr : frame.locals[103]? = some (.i64 normalizedPtr))
    (hCopiedBytes : frame.locals[104]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 110) 110 123 126
        (outputNode heap 768 3072 1).root 12288 result →
      Output heap initial final weights normalized (base + fcWeightOffset) (base + fcScaleOffset)
        (base + fcBiasOffset) 768 3072 1 true →
      wp «module» rest Q final result env) :
    wp «module» (expandedCode ++ rest) Q initial frame env := by
  have hBound := hWeights.1
  have hOffset (offset : Nat) (hOffset : offset ≤ blockBytes) : base + offset < UInt64.size := by
    change base + offset < 18446744073709551616
    omega
  have hWeightSafe := CheckedNatAdd.guard_of_fits base fcWeightOffset (hOffset _ (by decide))
  have hScaleSafe := CheckedNatAdd.guard_of_fits base fcScaleOffset (hOffset _ (by decide))
  have hBiasSafe := CheckedNatAdd.guard_of_fits base fcBiasOffset (hOffset _ (by decide))
  have hMatrix : base + fcWeightOffset + 768 * 3072 ≤ weights.size := by
    have : fcWeightOffset + 768 * 3072 ≤ blockBytes := by decide
    omega
  have hScales : base + fcScaleOffset + 3072 * 4 ≤ weights.size := by
    have : fcScaleOffset + 3072 * 4 ≤ blockBytes := by decide
    omega
  have hBias : base + fcBiasOffset + 3072 * 4 ≤ weights.size := by
    have : fcBiasOffset + 3072 * 4 ≤ blockBytes := by decide
    omega
  have hCall := GroupedProjection.Spec.linearGroupedRows_exact env initial heap
    weightsOwner weightsPtr normalizedPtr normalizedPtr weights normalized
    (base + fcWeightOffset) (base + fcScaleOffset) (base + fcBiasOffset) 768 3072 1 true
    hHeap hWeights hNormalized hMatrix hScales (fun _ => hBias) (by rw [hNormalizedSize])
    (by decide) (by decide) (by decide) hWeightsProtected hNormalizedProtected
    (by decide) (by decide) hResources.scales hResources.values hResources.output hPages
  simp only [hNormalizedSize, GroupedProjection.Projection.parameters, List.reverse_cons,
    List.reverse_nil, List.cons_append, List.nil_append] at hCall
  simp only [expandedCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hCopiedOwner, hCopiedPtr, hCopiedBytes]
  refine wp_call_tw (Layout.fcWeightOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, ← UInt64.ofNat_add]
  refine wp_call_tw (Layout.fcScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hScaleSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, ← UInt64.ofNat_add]
  refine wp_call_tw (Layout.fcBiasOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hBiasSafe)]
  wp_packed_frame [hParams, parameters, hLocals, ← UInt64.ofNat_add]
  refine wp_call_tw hCall ?_
  rintro final values ⟨rfl, hOutput⟩
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext _ _ ?_ hOutput
  simp (config := { maxDischargeDepth := 64 }) only [KernelState, parameters, hLocals,
    List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
    I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff,
    show UInt64.ofNat (4 * (1 * 3072)) = 12288 from rfl, and_self]

#print axioms expanded_spec
end Project.Gpt2QuantizedCached.CachedBlock
