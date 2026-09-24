import Project.Gpt2CachedStep.CachedBlock.Normalized
import Project.Gpt2CachedStep.CachedBlock.KernelState

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def normalized2Code : Wasm.Program :=
  [.localGet 0, .localSet 87, .localGet 1, .localSet 88, .localGet 2, .localSet 89,
   .localGet 84, .localSet 90, .localGet 85, .localSet 91, .localGet 86, .localSet 92,
   .localGet 11, .localSet 167, .call 7, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 93,
   .localGet 11, .localSet 167, .call 8, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 94,
   .constI64 1, .localSet 95,
   .localGet 87, .localGet 88, .localGet 89, .localGet 90, .localGet 91, .localGet 92,
   .localGet 93, .localGet 94, .localGet 95, .call 20,
   .localSet 98, .localSet 97, .localSet 96,
   .localGet 96, .localSet 99, .localGet 97, .localSet 100, .localGet 98, .localSet 101]

set_option maxRecDepth 32768 in
theorem emitted_normalized2 : (func33.drop 254).take 57 = normalized2Code := rfl

theorem normalized2_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr residualPtr : UInt64)
    (weights input cache residual : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hResidual : ByteArrayAt initial.mem residualPtr.toNat residual)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hResidualProtected : heap.Protects residualPtr.toNat (residualPtr.toNat + residual.size))
    (hResidualSize : residual.size = 3072)
    (hWeightsSize : (base + ln2BiasOffset + 768) * 4 ≤ weights.size)
    (hResources : LayerNorm.Resources heap 1 (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (hResidualOwner : frame.locals[73]? = some (.i64 residualPtr))
    (hResidualPtr : frame.locals[74]? = some (.i64 residualPtr))
    (hResidualBytes : frame.locals[75]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 76) 76 85 88
        (LayerNorm.outputNode heap 1).root 3072 result →
      result.get 90 = some (.i64 residualPtr) →
      (LayerNorm.finalHeap heap 1).At final →
      (LayerNorm.finalHeap heap 1).OwnsPacked final (LayerNorm.outputNode heap 1)
        (layerNorm weights residual (base + ln2ScaleOffset) (base + ln2BiasOffset) 1) →
      heap.Frame initial (LayerNorm.finalHeap heap 1) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 254).take 57 ++ rest) Q initial frame env := by
  have hScaleSize : (base + ln2ScaleOffset + 768) * 4 ≤ weights.size := by
    rw [Nat.add_assoc]
    exact (Nat.mul_le_mul_right 4 (Nat.le_add_right (base + ln2BiasOffset) 768)).trans hWeightsSize
  have hWeightFit : base + ln2ScaleOffset < UInt64.size := by
    have := hWeights.1
    change base + 2363904 < 18446744073709551616
    change (base + 2364672 + 768) * 4 ≤ weights.size at hWeightsSize
    omega
  have hBiasFit : base + ln2BiasOffset < UInt64.size := by
    have := hWeights.1
    change base + 2364672 < 18446744073709551616
    change (base + 2364672 + 768) * 4 ≤ weights.size at hWeightsSize
    omega
  have hWeightSafe := CheckedNatAdd.guard_of_fits base ln2ScaleOffset hWeightFit
  have hBiasSafe := CheckedNatAdd.guard_of_fits base ln2BiasOffset hBiasFit
  have hWeightAdd : UInt64.ofNat base + UInt64.ofNat ln2ScaleOffset = UInt64.ofNat (base + ln2ScaleOffset) :=
    (UInt64.ofNat_add _ _).symm
  have hBiasAdd : UInt64.ofNat base + UInt64.ofNat ln2BiasOffset = UInt64.ofNat (base + ln2BiasOffset) :=
    (UInt64.ofNat_add _ _).symm
  have hCall := LayerNorm.Spec.layerNorm_exact env initial heap weightsOwner residualPtr
    weightsPtr residualPtr weights residual (base + ln2ScaleOffset) (base + ln2BiasOffset) 1
    hHeap hWeights hResidual hWeightsProtected hResidualProtected (by rw [hResidualSize])
    hScaleSize hWeightsSize hResources hPages
  simp only [hResidualSize] at hCall
  rw [emitted_normalized2]
  simp only [normalized2Code, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hResidualOwner, hResidualPtr, hResidualBytes]
  refine wp_call_tw (Layout.ln2ScaleOffset_exact env initial) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, hWeightAdd]
  refine wp_call_tw (Layout.ln2BiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hBiasSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBiasAdd]
  refine wp_call_tw hCall ?_
  rintro final values ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  rw [LayerNorm.layerNorm_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [KernelState, parameters, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff,
      show UInt64.ofNat (4 * (1 * 768)) = 3072 from rfl, and_self]
  · simp only [Locals.get, hParams, parameters, hLocals, List.length_cons, List.length_nil,
      List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT,
      Nat.reduceSub, reduceIte]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms normalized2_spec

end Project.Gpt2CachedStep.CachedBlock
