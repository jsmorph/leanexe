import Project.Gpt2QuantizedCached.CachedBlock.Normalized
import Project.Gpt2QuantizedCached.GroupedProjection.Fresh

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized GroupedProjection.Projection

def normalizedSuccess : Wasm.Program :=
  match (func54[107]? : Option Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

def QkvState (params : List Value) (base : Nat) (normalizedPtr qkvPtr : UInt64) (frame : Locals) : Prop :=
  NormalizedState params base normalizedPtr frame ∧
  frame.locals[34]? = some (.i64 qkvPtr) ∧ frame.locals[35]? = some (.i64 qkvPtr) ∧
  frame.locals[36]? = some (.i64 9216) ∧ frame.locals[37]? = some (.i64 qkvPtr) ∧
  frame.locals[38]? = some (.i64 qkvPtr) ∧ frame.locals[39]? = some (.i64 9216)

def qkvCode : Wasm.Program := [
   .localGet 0,
   .localSet 32,
   .localGet 1,
   .localSet 33,
   .localGet 2,
   .localSet 34,
   .localGet 24,
   .localSet 35,
   .localGet 25,
   .localSet 36,
   .localGet 26,
   .localSet 37,
   .localGet 11,
   .localSet 196,
   .call 5,
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
   .localSet 38,
   .localGet 11,
   .localSet 196,
   .call 6,
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
   .localSet 39,
   .localGet 11,
   .localSet 196,
   .call 7,
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
   .localSet 40,
   .constI64 768,
   .localSet 41,
   .constI64 2304,
   .localSet 42,
   .constI64 1,
   .localSet 43,
   .constI64 1,
   .localSet 44,
   .localGet 32,
   .localGet 33,
   .localGet 34,
   .localGet 35,
   .localGet 36,
   .localGet 37,
   .localGet 38,
   .localGet 39,
   .localGet 40,
   .localGet 41,
   .localGet 42,
   .localGet 43,
   .localGet 44,
   .call 42,
   .localSet 47,
   .localSet 46,
   .localSet 45,
   .localGet 45,
   .localSet 48,
   .localGet 46,
   .localSet 49,
   .localGet 47,
   .localSet 50
  ]

theorem emitted_qkv : normalizedSuccess.take 79 = qkvCode := rfl

theorem qkv_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr normalizedPtr : UInt64)
    (weights input cache normalized : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hNormalized : ByteArrayAt initial.mem normalizedPtr.toNat normalized)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hNormalizedProtected : heap.Protects normalizedPtr.toNat (normalizedPtr.toNat + normalized.size))
    (hNormalizedSize : normalized.size = 3072)
    (hExtent : base + blockBytes ≤ weights.size)
    (hResources : Resources heap 768 2304 1 (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : NormalizedState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position) base normalizedPtr frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      QkvState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) base normalizedPtr (outputNode heap 768 2304 1).root result →
      Output heap initial final weights normalized (base + qkvWeightOffset) (base + qkvScaleOffset)
        (base + qkvBiasOffset) 768 2304 1 true →
      wp «module» rest Q final result env) :
    wp «module» (qkvCode ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hBase, hNormalizedOwner, hNormalizedPtr,
    hNormalizedBytes, hCopiedOwner, hCopiedPtr, hCopiedBytes, hTyped⟩
  have hBound := hWeights.1
  have hOffset (offset : Nat) (hOffset : offset ≤ blockBytes) : base + offset < UInt64.size := by
    change base + offset < 18446744073709551616
    omega
  have hWeightSafe := CheckedNatAdd.guard_of_fits base qkvWeightOffset (hOffset _ (by decide))
  have hScaleSafe := CheckedNatAdd.guard_of_fits base qkvScaleOffset (hOffset _ (by decide))
  have hBiasSafe := CheckedNatAdd.guard_of_fits base qkvBiasOffset (hOffset _ (by decide))
  have hMatrix : base + qkvWeightOffset + 768 * 2304 ≤ weights.size := by
    have : qkvWeightOffset + 768 * 2304 ≤ blockBytes := by decide
    omega
  have hScales : base + qkvScaleOffset + 2304 * 4 ≤ weights.size := by
    have : qkvScaleOffset + 2304 * 4 ≤ blockBytes := by decide
    omega
  have hBias : base + qkvBiasOffset + 2304 * 4 ≤ weights.size := by
    have : qkvBiasOffset + 2304 * 4 ≤ blockBytes := by decide
    omega
  have hCall := GroupedProjection.Spec.linearGroupedRows_exact env initial heap
    weightsOwner weightsPtr normalizedPtr normalizedPtr weights normalized
    (base + qkvWeightOffset) (base + qkvScaleOffset) (base + qkvBiasOffset) 768 2304 1 true
    hHeap hWeights hNormalized hMatrix hScales (fun _ => hBias) (by rw [hNormalizedSize])
    (by decide) (by decide) (by decide) hWeightsProtected hNormalizedProtected
    (by decide) (by decide) hResources.scales hResources.values hResources.output hPages
  simp only [hNormalizedSize, GroupedProjection.Projection.parameters, List.reverse_cons,
    List.reverse_nil, List.cons_append, List.nil_append] at hCall
  simp only [qkvCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hCopiedOwner, hCopiedPtr, hCopiedBytes]
  refine wp_call_tw (Layout.qkvWeightOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, ← UInt64.ofNat_add]
  refine wp_call_tw (Layout.qkvScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hScaleSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, ← UInt64.ofNat_add]
  refine wp_call_tw (Layout.qkvBiasOffset_exact env initial) ?_
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
  simp (config := { maxDischargeDepth := 64 }) only [QkvState, NormalizedState, parameters, hLocals,
    List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, hBase,
    hNormalizedOwner, hNormalizedPtr, hNormalizedBytes, hCopiedOwner, hCopiedPtr, hCopiedBytes,
    I64Values.set, hTyped, show UInt64.ofNat (4 * (1 * 2304)) = 9216 from rfl, and_self]

#print axioms qkv_spec
end Project.Gpt2QuantizedCached.CachedBlock
