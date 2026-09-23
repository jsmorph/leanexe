import Project.Gpt2QuantizedCached.CachedBlock.Structure
import Project.Gpt2QuantizedCached.CachedBlock.KernelState

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized GroupedProjection.Projection

def projected2Code : Wasm.Program := [
   .localGet 0,
   .localSet 154,
   .localGet 1,
   .localSet 155,
   .localGet 2,
   .localSet 156,
   .localGet 146,
   .localSet 157,
   .localGet 147,
   .localSet 158,
   .localGet 148,
   .localSet 159,
   .localGet 11,
   .localSet 196,
   .call 16,
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
   .localSet 160,
   .localGet 11,
   .localSet 196,
   .call 17,
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
   .localSet 161,
   .localGet 11,
   .localSet 196,
   .call 18,
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
   .localSet 162,
   .constI64 3072,
   .localSet 163,
   .constI64 768,
   .localSet 164,
   .constI64 1,
   .localSet 165,
   .constI64 1,
   .localSet 166,
   .localGet 154,
   .localGet 155,
   .localGet 156,
   .localGet 157,
   .localGet 158,
   .localGet 159,
   .localGet 160,
   .localGet 161,
   .localGet 162,
   .localGet 163,
   .localGet 164,
   .localGet 165,
   .localGet 166,
   .call 42,
   .localSet 169,
   .localSet 168,
   .localSet 167,
   .localGet 167,
   .localSet 170,
   .localGet 168,
   .localSet 171,
   .localGet 169,
   .localSet 172
  ]

theorem emitted_projected2 : activatedSuccess.take 79 = projected2Code := rfl

theorem projected2_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr normalizedPtr : UInt64)
    (weights input cache normalized : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hNormalized : ByteArrayAt initial.mem normalizedPtr.toNat normalized)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hNormalizedProtected : heap.Protects normalizedPtr.toNat (normalizedPtr.toNat + normalized.size))
    (hNormalizedSize : normalized.size = 12288)
    (hExtent : base + blockBytes ≤ weights.size)
    (hResources : Resources heap 3072 768 1 (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 193) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (hCopiedOwner : frame.locals[135]? = some (.i64 normalizedPtr))
    (hCopiedPtr : frame.locals[136]? = some (.i64 normalizedPtr))
    (hCopiedBytes : frame.locals[137]? = some (.i64 12288))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 143) 143 156 159
        (outputNode heap 3072 768 1).root 3072 result →
      Output heap initial final weights normalized (base + mlpWeightOffset) (base + mlpScaleOffset)
        (base + mlpBiasOffset) 3072 768 1 true →
      wp «module» rest Q final result env) :
    wp «module» (projected2Code ++ rest) Q initial frame env := by
  have hBound := hWeights.1
  have hOffset (offset : Nat) (hOffset : offset ≤ blockBytes) : base + offset < UInt64.size := by
    change base + offset < 18446744073709551616
    omega
  have hWeightSafe := CheckedNatAdd.guard_of_fits base mlpWeightOffset (hOffset _ (by decide))
  have hScaleSafe := CheckedNatAdd.guard_of_fits base mlpScaleOffset (hOffset _ (by decide))
  have hBiasSafe := CheckedNatAdd.guard_of_fits base mlpBiasOffset (hOffset _ (by decide))
  have hMatrix : base + mlpWeightOffset + 3072 * 768 ≤ weights.size := by
    have : mlpWeightOffset + 3072 * 768 ≤ blockBytes := by decide
    omega
  have hScales : base + mlpScaleOffset + 768 * 4 ≤ weights.size := by
    have : mlpScaleOffset + 768 * 4 ≤ blockBytes := by decide
    omega
  have hBias : base + mlpBiasOffset + 768 * 4 ≤ weights.size := by
    have : mlpBiasOffset + 768 * 4 ≤ blockBytes := by decide
    omega
  have hCall := GroupedProjection.Spec.linearGroupedRows_exact env initial heap
    weightsOwner weightsPtr normalizedPtr normalizedPtr weights normalized
    (base + mlpWeightOffset) (base + mlpScaleOffset) (base + mlpBiasOffset) 3072 768 1 true
    hHeap hWeights hNormalized hMatrix hScales (fun _ => hBias) (by rw [hNormalizedSize])
    (by decide) (by decide) (by decide) hWeightsProtected hNormalizedProtected
    (by decide) (by decide) hResources.scales hResources.values hResources.output hPages
  simp only [hNormalizedSize, GroupedProjection.Projection.parameters, List.reverse_cons,
    List.reverse_nil, List.cons_append, List.nil_append] at hCall
  simp only [projected2Code, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hCopiedOwner, hCopiedPtr, hCopiedBytes]
  refine wp_call_tw (Layout.mlpWeightOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, ← UInt64.ofNat_add]
  refine wp_call_tw (Layout.mlpScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hScaleSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, ← UInt64.ofNat_add]
  refine wp_call_tw (Layout.mlpBiasOffset_exact env initial) ?_
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
    show UInt64.ofNat (4 * (1 * 768)) = 3072 from rfl, and_self]

#print axioms projected2_spec
end Project.Gpt2QuantizedCached.CachedBlock
