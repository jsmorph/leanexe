import Project.Gpt2CachedStep.CachedBlock.Normalized
import Project.Gpt2CachedStep.CachedBlock.KernelState
import Project.Gpt2CachedStep.LinearRows.Heap

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def projectionNeed : UInt64 := PackedCapacity.capacity 3072

def projectionCode : Wasm.Program :=
  [.localGet 0, .localSet 58, .localGet 1, .localSet 59, .localGet 2, .localSet 60,
   .localGet 55, .localSet 61, .localGet 56, .localSet 62, .localGet 57, .localSet 63,
   .localGet 11, .localSet 167, .call 5, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 64,
   .localGet 11, .localSet 167, .call 6, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 65,
   .constI64 768, .localSet 66, .constI64 768, .localSet 67, .constI64 1, .localSet 68,
   .localGet 58, .localGet 59, .localGet 60, .localGet 61, .localGet 62, .localGet 63,
   .localGet 64, .localGet 65, .localGet 66, .localGet 67, .localGet 68, .call 21,
   .localSet 71, .localSet 70, .localSet 69,
   .localGet 69, .localSet 72, .localGet 70, .localSet 73, .localGet 71, .localSet 74]

set_option maxRecDepth 32768 in
theorem emitted_projection : (func33.drop 163).take 63 = projectionCode := rfl

theorem projection_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr attentionPtr : UInt64)
    (weights input cache attention : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hAttention : ByteArrayAt initial.mem attentionPtr.toNat attention)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hAttentionProtected : heap.Protects attentionPtr.toNat (attentionPtr.toNat + attention.size))
    (hAttentionSize : attention.size = 3072)
    (hWeightsSize : (base + attnBiasOffset + 768) * 4 ≤ weights.size)
    (hResources : LayerNorm.AllocationFits heap projectionNeed (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (hAttentionOwner : frame.locals[44]? = some (.i64 attentionPtr))
    (hAttentionPtr : frame.locals[45]? = some (.i64 attentionPtr))
    (hAttentionBytes : frame.locals[46]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 47) 47 58 61
        (allocatedNode heap.top projectionNeed heap.nodes).root 3072 result →
      (heap.allocate projectionNeed).At final →
      (heap.allocate projectionNeed).OwnsPacked final (allocatedNode heap.top projectionNeed heap.nodes)
        (linearRows weights attention (base + attnWeightOffset) (base + attnBiasOffset) 768 768 1) →
      heap.Frame initial (heap.allocate projectionNeed) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 163).take 63 ++ rest) Q initial frame env := by
  have hMatrixSize : (base + attnWeightOffset + 768 * 768) * 4 ≤ weights.size := by
    rw [Nat.add_assoc]
    exact (Nat.mul_le_mul_right 4 (Nat.le_add_right (base + attnBiasOffset) 768)).trans hWeightsSize
  have hWeightFit : base + attnWeightOffset < UInt64.size := by
    have := hWeights.1
    change base + 1773312 < 18446744073709551616
    change (base + 2363136 + 768) * 4 ≤ weights.size at hWeightsSize
    omega
  have hBiasFit : base + attnBiasOffset < UInt64.size := by
    have := hWeights.1
    change base + 2363136 < 18446744073709551616
    change (base + 2363136 + 768) * 4 ≤ weights.size at hWeightsSize
    omega
  have hWeightSafe := CheckedNatAdd.guard_of_fits base attnWeightOffset hWeightFit
  have hBiasSafe := CheckedNatAdd.guard_of_fits base attnBiasOffset hBiasFit
  have hWeightAdd : UInt64.ofNat base + UInt64.ofNat attnWeightOffset = UInt64.ofNat (base + attnWeightOffset) :=
    (UInt64.ofNat_add _ _).symm
  have hBiasAdd : UInt64.ofNat base + UInt64.ofNat attnBiasOffset = UInt64.ofNat (base + attnBiasOffset) :=
    (UInt64.ofNat_add _ _).symm
  have hCall := LinearRows.Spec.linearRows_owned env initial heap weightsOwner attentionPtr
    weightsPtr attentionPtr weights attention (base + attnWeightOffset) (base + attnBiasOffset) 768 768 1
    hHeap hWeights hAttention (by rw [hAttentionSize]) hMatrixSize hWeightsSize
    (by decide) (by decide) (by decide) hResources hPages hWeightsProtected hAttentionProtected
  simp only [hAttentionSize] at hCall
  rw [emitted_projection]
  simp only [projectionCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hAttentionOwner, hAttentionPtr, hAttentionBytes]
  refine wp_call_tw (Layout.attnWeightOffset_exact env initial) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, hWeightAdd]
  refine wp_call_tw (Layout.attnBiasOffset_exact env _) ?_
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
  · simp (config := { maxDischargeDepth := 64 }) only [KernelState, parameters, projectionNeed, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff,
      show UInt64.ofNat (4 * (1 * 768)) = 3072 from rfl, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms projection_spec

end Project.Gpt2CachedStep.CachedBlock
