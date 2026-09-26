import Project.Gpt2QuantizedCached.CachedBlock.Normalized
import Project.Gpt2QuantizedCached.CachedBlock.KernelState
import Project.Gpt2QuantizedCached.CachedBlock.Structure

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2
open LeanExe.Models.Gpt2.Quantized (blockBytes)

def normalized2Code : Wasm.Program := [
    .localGet 0,
    .localSet 101,
    .localGet 1,
    .localSet 102,
    .localGet 2,
    .localSet 103,
    .localGet 98,
    .localSet 104,
    .localGet 99,
    .localSet 105,
    .localGet 100,
    .localSet 106,
    .localGet 11,
    .localSet 198,
    .call 11,
    .localSet 199,
    .localGet 198,
    .localGet 199,
    .addI64,
    .localTee 200,
    .localGet 198,
    .ltUI64,
    .iff 0 1 [
     .unreachable
    ] [
     .localGet 200
    ] [] [.i64],
    .localSet 196,
    .constI64 4,
    .localSet 197,
    .localGet 197,
    .constI64 0,
    .eqI64,
    .iff 0 1 [
     .constI64 0
    ] [
     .localGet 196,
     .localGet 197,
     .divUI64
    ] [] [.i64],
    .localSet 107,
    .localGet 11,
    .localSet 198,
    .call 12,
    .localSet 199,
    .localGet 198,
    .localGet 199,
    .addI64,
    .localTee 200,
    .localGet 198,
    .ltUI64,
    .iff 0 1 [
     .unreachable
    ] [
     .localGet 200
    ] [] [.i64],
    .localSet 196,
    .constI64 4,
    .localSet 197,
    .localGet 197,
    .constI64 0,
    .eqI64,
    .iff 0 1 [
     .constI64 0
    ] [
     .localGet 196,
     .localGet 197,
     .divUI64
    ] [] [.i64],
    .localSet 108,
    .constI64 1,
    .localSet 109,
    .localGet 101,
    .localGet 102,
    .localGet 103,
    .localGet 104,
    .localGet 105,
    .localGet 106,
    .localGet 107,
    .localGet 108,
    .localGet 109,
    .call 34,
    .localSet 112,
    .localSet 111,
    .localSet 110,
    .localGet 110,
    .localSet 113,
    .localGet 111,
    .localSet 114,
    .localGet 112,
    .localSet 115
  ]

set_option maxRecDepth 32768 in
theorem emitted_normalized2 : (attentionSuccess.drop 107).take 71 = normalized2Code := rfl

theorem normalized2_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr residualPtr : UInt64)
    (weights input cache residual : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hResidual : ByteArrayAt initial.mem residualPtr.toNat residual)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hResidualProtected : heap.Protects residualPtr.toNat (residualPtr.toNat + residual.size))
    (hResidualSize : residual.size = 3072)
    (hExtent : base + blockBytes ≤ weights.size)
    (hResources : Gpt2CachedStep.LayerNorm.Resources heap 1 (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 193) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (hResidualOwner : frame.locals[87]? = some (.i64 residualPtr))
    (hResidualPtr : frame.locals[88]? = some (.i64 residualPtr))
    (hResidualBytes : frame.locals[89]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 90) 90 99 102
        (Gpt2CachedStep.LayerNorm.outputNode heap 1).root 3072 result →
      (Gpt2CachedStep.LayerNorm.finalHeap heap 1).At final →
      (Gpt2CachedStep.LayerNorm.finalHeap heap 1).OwnsPacked final (Gpt2CachedStep.LayerNorm.outputNode heap 1)
        (layerNorm weights residual ((base + Quantized.ln2ScaleOffset) / 4) ((base + Quantized.ln2BiasOffset) / 4) 1) →
      heap.Frame initial (Gpt2CachedStep.LayerNorm.finalHeap heap 1) final →
      final.mem.pages ≤ 65536 → final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0 →
      wp «module» rest Q final result env) :
    wp «module» (normalized2Code ++ rest) Q initial frame env := by
  have hBound := hWeights.1
  have hFit (offset : Nat) (hOffset : offset ≤ blockBytes) : base + offset < UInt64.size := by
    change base + offset < 18446744073709551616
    omega
  have hWeightFit := hFit Quantized.ln2ScaleOffset (by decide)
  have hBiasFit := hFit Quantized.ln2BiasOffset (by decide)
  have hSlice (offset : Nat) (hOffset : offset + 3072 ≤ blockBytes) :
      ((base + offset) / 4 + 768) * 4 ≤ weights.size := by
    calc
      _ = (base + offset) / 4 * 4 + 3072 := by rw [Nat.add_mul]
      _ ≤ base + offset + 3072 := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
      _ = base + (offset + 3072) := Nat.add_assoc _ _ _
      _ ≤ base + blockBytes := Nat.add_le_add_left hOffset base
      _ ≤ weights.size := hExtent
  have hScaleSize := hSlice Quantized.ln2ScaleOffset (by decide)
  have hBiasSize := hSlice Quantized.ln2BiasOffset (by decide)
  have hWeightSafe := CheckedNatAdd.guard_of_fits base Quantized.ln2ScaleOffset hWeightFit
  have hBiasSafe := CheckedNatAdd.guard_of_fits base Quantized.ln2BiasOffset hBiasFit
  have hWeightDiv : UInt64.ofNat (base + Quantized.ln2ScaleOffset) / 4 =
      UInt64.ofNat ((base + Quantized.ln2ScaleOffset) / 4) :=
    (UInt64.ofNat_div hWeightFit (by decide)).symm
  have hBiasDiv : UInt64.ofNat (base + Quantized.ln2BiasOffset) / 4 =
      UInt64.ofNat ((base + Quantized.ln2BiasOffset) / 4) :=
    (UInt64.ofNat_div hBiasFit (by decide)).symm
  have hCall := LayerNorm.layerNorm_exact env initial heap weightsOwner residualPtr
    weightsPtr residualPtr weights residual ((base + Quantized.ln2ScaleOffset) / 4)
    ((base + Quantized.ln2BiasOffset) / 4) 1
    hHeap hWeights hResidual hWeightsProtected hResidualProtected (by rw [hResidualSize])
    hScaleSize hBiasSize hResources hPages
  simp only [hResidualSize] at hCall
  simp only [normalized2Code, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hResidualOwner, hResidualPtr, hResidualBytes]
  refine wp_call_tw (Layout.ln2ScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, hWeightDiv]
  refine wp_call_tw (Layout.ln2BiasOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hBiasSafe)]
  wp_packed_frame [hParams, parameters, hLocals, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, parameters, hLocals, hBiasDiv]
  refine wp_call_tw hCall ?_
  rintro final values ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  rw [Gpt2CachedStep.LayerNorm.layerNorm_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [KernelState, parameters, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff,
      show UInt64.ofNat (4 * (1 * 768)) = 3072 from rfl, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms normalized2_spec

end Project.Gpt2QuantizedCached.CachedBlock
