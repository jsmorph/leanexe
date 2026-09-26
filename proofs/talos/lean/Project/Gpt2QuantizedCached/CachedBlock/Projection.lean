import Project.Gpt2QuantizedCached.CachedBlock.Structure
import Project.Gpt2QuantizedCached.CachedBlock.KernelState

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized GroupedProjection.Projection

def projectionCode : Wasm.Program := [
   .localGet 0,
   .localSet 70,
   .localGet 1,
   .localSet 71,
   .localGet 2,
   .localSet 72,
   .localGet 62,
   .localSet 73,
   .localGet 63,
   .localSet 74,
   .localGet 64,
   .localSet 75,
   .localGet 11,
   .localSet 196,
   .call 8,
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
   .localSet 76,
   .localGet 11,
   .localSet 196,
   .call 9,
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
   .localSet 77,
   .localGet 11,
   .localSet 196,
   .call 10,
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
   .localSet 78,
   .constI64 768,
   .localSet 79,
   .constI64 768,
   .localSet 80,
   .constI64 1,
   .localSet 81,
   .constI64 1,
   .localSet 82,
   .localGet 70,
   .localGet 71,
   .localGet 72,
   .localGet 73,
   .localGet 74,
   .localGet 75,
   .localGet 76,
   .localGet 77,
   .localGet 78,
   .localGet 79,
   .localGet 80,
   .localGet 81,
   .localGet 82,
   .call 42,
   .localSet 85,
   .localSet 84,
   .localSet 83,
   .localGet 83,
   .localSet 86,
   .localGet 84,
   .localSet 87,
   .localGet 85,
   .localSet 88
  ]

theorem emitted_projection : attentionSuccess.take 79 = projectionCode := rfl

theorem projection_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr normalizedPtr : UInt64)
    (weights input cache normalized : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hNormalized : ByteArrayAt initial.mem normalizedPtr.toNat normalized)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hNormalizedProtected : heap.Protects normalizedPtr.toNat (normalizedPtr.toNat + normalized.size))
    (hNormalizedSize : normalized.size = 3072)
    (hExtent : base + blockBytes ≤ weights.size)
    (hResources : Resources heap 768 768 1 (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 193) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (hCopiedOwner : frame.locals[51]? = some (.i64 normalizedPtr))
    (hCopiedPtr : frame.locals[52]? = some (.i64 normalizedPtr))
    (hCopiedBytes : frame.locals[53]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 59) 59 72 75
        (outputNode heap 768 768 1).root 3072 result →
      Output heap initial final weights normalized (base + attnWeightOffset) (base + attnScaleOffset)
        (base + attnBiasOffset) 768 768 1 true →
      wp «module» rest Q final result env) :
    wp «module» (projectionCode ++ rest) Q initial frame env := by
  have hBound := hWeights.1
  have hOffset (offset : Nat) (hOffset : offset ≤ blockBytes) : base + offset < UInt64.size := by
    change base + offset < 18446744073709551616
    omega
  have hWeightSafe := CheckedNatAdd.guard_of_fits base attnWeightOffset (hOffset _ (by decide))
  have hScaleSafe := CheckedNatAdd.guard_of_fits base attnScaleOffset (hOffset _ (by decide))
  have hBiasSafe := CheckedNatAdd.guard_of_fits base attnBiasOffset (hOffset _ (by decide))
  have hMatrix : base + attnWeightOffset + 768 * 768 ≤ weights.size := by
    have : attnWeightOffset + 768 * 768 ≤ blockBytes := by decide
    omega
  have hScales : base + attnScaleOffset + 768 * 4 ≤ weights.size := by
    have : attnScaleOffset + 768 * 4 ≤ blockBytes := by decide
    omega
  have hBias : base + attnBiasOffset + 768 * 4 ≤ weights.size := by
    have : attnBiasOffset + 768 * 4 ≤ blockBytes := by decide
    omega
  have hCall := GroupedProjection.Spec.linearGroupedRows_exact env initial heap
    weightsOwner weightsPtr normalizedPtr normalizedPtr weights normalized
    (base + attnWeightOffset) (base + attnScaleOffset) (base + attnBiasOffset) 768 768 1 true
    hHeap hWeights hNormalized hMatrix hScales (fun _ => hBias) (by rw [hNormalizedSize])
    (by decide) (by decide) (by decide) hWeightsProtected hNormalizedProtected
    (by decide) (by decide) hResources.scales hResources.values hResources.output hPages
  simp only [hNormalizedSize, GroupedProjection.Projection.parameters, List.reverse_cons,
    List.reverse_nil, List.cons_append, List.nil_append] at hCall
  simp only [projectionCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hCopiedOwner, hCopiedPtr, hCopiedBytes]
  refine wp_call_tw (Layout.attnWeightOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, ← UInt64.ofNat_add]
  refine wp_call_tw (Layout.attnScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hScaleSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, ← UInt64.ofNat_add]
  refine wp_call_tw (Layout.attnBiasOffset_exact env initial) ?_
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

#print axioms projection_spec
end Project.Gpt2QuantizedCached.CachedBlock
