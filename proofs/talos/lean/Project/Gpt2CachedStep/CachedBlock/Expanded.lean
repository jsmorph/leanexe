import Project.Gpt2CachedStep.CachedBlock.Normalized
import Project.Gpt2CachedStep.CachedBlock.KernelState
import Project.Gpt2CachedStep.LinearRows.Heap

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def expandedNeed : UInt64 := PackedCapacity.capacity 12288

def expandedCode : Wasm.Program :=
  [.localGet 0, .localSet 102, .localGet 1, .localSet 103, .localGet 2, .localSet 104,
   .localGet 99, .localSet 105, .localGet 100, .localSet 106, .localGet 101, .localSet 107,
   .localGet 11, .localSet 167, .call 9, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 108,
   .localGet 11, .localSet 167, .call 10, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 109,
   .constI64 768, .localSet 110, .constI64 3072, .localSet 111, .constI64 1, .localSet 112,
   .localGet 102, .localGet 103, .localGet 104, .localGet 105, .localGet 106, .localGet 107,
   .localGet 108, .localGet 109, .localGet 110, .localGet 111, .localGet 112, .call 21,
   .localSet 115, .localSet 114, .localSet 113,
   .localGet 113, .localSet 116, .localGet 114, .localSet 117, .localGet 115, .localSet 118]

set_option maxRecDepth 32768 in
theorem emitted_expanded : (func33.drop 311).take 63 = expandedCode := rfl

theorem expanded_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr normalized2Ptr : UInt64)
    (weights input cache normalized2 : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hNormalized2 : ByteArrayAt initial.mem normalized2Ptr.toNat normalized2)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hNormalized2Protected : heap.Protects normalized2Ptr.toNat (normalized2Ptr.toNat + normalized2.size))
    (hNormalized2Size : normalized2.size = 3072)
    (hWeightsSize : (base + fcBiasOffset + 3072) * 4 ≤ weights.size)
    (hResources : LayerNorm.AllocationFits heap expandedNeed (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (hNormalized2Owner : frame.locals[88]? = some (.i64 normalized2Ptr))
    (hNormalized2Ptr : frame.locals[89]? = some (.i64 normalized2Ptr))
    (hNormalized2Bytes : frame.locals[90]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 91) 91 102 105
        (allocatedNode heap.top expandedNeed heap.nodes).root 12288 result →
      (heap.allocate expandedNeed).At final →
      (heap.allocate expandedNeed).OwnsPacked final (allocatedNode heap.top expandedNeed heap.nodes)
        (linearRows weights normalized2 (base + fcWeightOffset) (base + fcBiasOffset) 768 3072 1) →
      heap.Frame initial (heap.allocate expandedNeed) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 311).take 63 ++ rest) Q initial frame env := by
  have hMatrixSize : (base + fcWeightOffset + 768 * 3072) * 4 ≤ weights.size := by
    rw [Nat.add_assoc]
    exact (Nat.mul_le_mul_right 4 (Nat.le_add_right (base + fcBiasOffset) 3072)).trans hWeightsSize
  have hWeightFit : base + fcWeightOffset < UInt64.size := by
    have := hWeights.1
    change base + 2365440 < 18446744073709551616
    change (base + 4724736 + 3072) * 4 ≤ weights.size at hWeightsSize
    omega
  have hBiasFit : base + fcBiasOffset < UInt64.size := by
    have := hWeights.1
    change base + 4724736 < 18446744073709551616
    change (base + 4724736 + 3072) * 4 ≤ weights.size at hWeightsSize
    omega
  have hWeightSafe := CheckedNatAdd.guard_of_fits base fcWeightOffset hWeightFit
  have hBiasSafe := CheckedNatAdd.guard_of_fits base fcBiasOffset hBiasFit
  have hWeightAdd : UInt64.ofNat base + UInt64.ofNat fcWeightOffset = UInt64.ofNat (base + fcWeightOffset) :=
    (UInt64.ofNat_add _ _).symm
  have hBiasAdd : UInt64.ofNat base + UInt64.ofNat fcBiasOffset = UInt64.ofNat (base + fcBiasOffset) :=
    (UInt64.ofNat_add _ _).symm
  have hCall := LinearRows.Spec.linearRows_owned env initial heap weightsOwner normalized2Ptr
    weightsPtr normalized2Ptr weights normalized2 (base + fcWeightOffset) (base + fcBiasOffset) 768 3072 1
    hHeap hWeights hNormalized2 (by rw [hNormalized2Size]) hMatrixSize hWeightsSize
    (by decide) (by decide) (by decide) hResources hPages hWeightsProtected hNormalized2Protected
  simp only [hNormalized2Size] at hCall
  rw [emitted_expanded]
  simp only [expandedCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hNormalized2Owner, hNormalized2Ptr, hNormalized2Bytes]
  refine wp_call_tw (Layout.fcWeightOffset_exact env initial) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, hWeightAdd]
  refine wp_call_tw (Layout.fcBiasOffset_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hBiasSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBiasAdd]
  refine wp_call_tw hCall ?_
  rintro final values ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  rw [Project.Gpt2LinearRows.linearRows_eq, PackedSource.generate_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [KernelState, parameters, expandedNeed, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff,
      show UInt64.ofNat (4 * (1 * 3072)) = 12288 from rfl, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms expanded_spec

end Project.Gpt2CachedStep.CachedBlock
