import Project.Gpt2CachedStep.CachedBlock.FrozenNormalized
import Project.Gpt2CachedStep.CachedBlock.FrozenKernelState
import Project.Gpt2CachedStep.LinearRows.FrozenHeap

namespace Project.Gpt2CachedStep.Frozen.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def projected2Need : UInt64 := PackedCapacity.capacity 3072

def projected2Code : Wasm.Program :=
  [.localGet 0, .localSet 128, .localGet 1, .localSet 129, .localGet 2, .localSet 130,
   .localGet 125, .localSet 131, .localGet 126, .localSet 132, .localGet 127, .localSet 133,
   .localGet 11, .localSet 167, .call 11, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 134,
   .localGet 11, .localSet 167, .call 12, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 135,
   .constI64 3072, .localSet 136, .constI64 768, .localSet 137, .constI64 1, .localSet 138,
   .localGet 128, .localGet 129, .localGet 130, .localGet 131, .localGet 132, .localGet 133,
   .localGet 134, .localGet 135, .localGet 136, .localGet 137, .localGet 138, .call 21,
   .localSet 141, .localSet 140, .localSet 139,
   .localGet 139, .localSet 142, .localGet 140, .localSet 143, .localGet 141, .localSet 144]

set_option maxRecDepth 32768 in
theorem emitted_projected2 : (func33.drop 393).take 63 = projected2Code := rfl

theorem projected2_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr activatedPtr : UInt64)
    (weights input cache activated : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hActivated : ByteArrayAt initial.mem activatedPtr.toNat activated)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hActivatedProtected : heap.Protects activatedPtr.toNat (activatedPtr.toNat + activated.size))
    (hActivatedSize : activated.size = 12288)
    (hWeightsSize : (base + mlpBiasOffset + 768) * 4 ≤ weights.size)
    (hResources : LayerNorm.AllocationFits heap projected2Need (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (hActivatedOwner : frame.locals[114]? = some (.i64 activatedPtr))
    (hActivatedPtr : frame.locals[115]? = some (.i64 activatedPtr))
    (hActivatedBytes : frame.locals[116]? = some (.i64 12288))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      KernelState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 117) 117 128 131
        (allocatedNode heap.top projected2Need heap.nodes).root 3072 result →
      (heap.allocate projected2Need).At final →
      (heap.allocate projected2Need).OwnsPacked final (allocatedNode heap.top projected2Need heap.nodes)
        (linearRows weights activated (base + mlpWeightOffset) (base + mlpBiasOffset) 3072 768 1) →
      heap.Frame initial (heap.allocate projected2Need) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 393).take 63 ++ rest) Q initial frame env := by
  have hMatrixSize : (base + mlpWeightOffset + 3072 * 768) * 4 ≤ weights.size := by
    rw [Nat.add_assoc]
    exact (Nat.mul_le_mul_right 4 (Nat.le_add_right (base + mlpBiasOffset) 768)).trans hWeightsSize
  have hWeightFit : base + mlpWeightOffset < UInt64.size := by
    have := hWeights.1
    change base + 4727808 < 18446744073709551616
    change (base + 7087104 + 768) * 4 ≤ weights.size at hWeightsSize
    omega
  have hBiasFit : base + mlpBiasOffset < UInt64.size := by
    have := hWeights.1
    change base + 7087104 < 18446744073709551616
    change (base + 7087104 + 768) * 4 ≤ weights.size at hWeightsSize
    omega
  have hWeightSafe := CheckedNatAdd.guard_of_fits base mlpWeightOffset hWeightFit
  have hBiasSafe := CheckedNatAdd.guard_of_fits base mlpBiasOffset hBiasFit
  have hWeightAdd : UInt64.ofNat base + UInt64.ofNat mlpWeightOffset = UInt64.ofNat (base + mlpWeightOffset) :=
    (UInt64.ofNat_add _ _).symm
  have hBiasAdd : UInt64.ofNat base + UInt64.ofNat mlpBiasOffset = UInt64.ofNat (base + mlpBiasOffset) :=
    (UInt64.ofNat_add _ _).symm
  have hCall := LinearRows.Spec.linearRows_owned env initial heap weightsOwner activatedPtr
    weightsPtr activatedPtr weights activated (base + mlpWeightOffset) (base + mlpBiasOffset) 3072 768 1
    hHeap hWeights hActivated (by rw [hActivatedSize]) hMatrixSize hWeightsSize
    (by decide) (by decide) (by decide) hResources hPages hWeightsProtected hActivatedProtected
  simp only [hActivatedSize] at hCall
  rw [emitted_projected2]
  simp only [projected2Code, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hActivatedOwner, hActivatedPtr, hActivatedBytes]
  refine wp_call_tw (Layout.mlpWeightOffset_exact env initial) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, parameters, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, hWeightAdd]
  refine wp_call_tw (Layout.mlpBiasOffset_exact env _) ?_
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
  · simp (config := { maxDischargeDepth := 64 }) only [KernelState, parameters, projected2Need, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceAdd, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff,
      show UInt64.ofNat (4 * (1 * 768)) = 3072 from rfl, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms projected2_spec

end Project.Gpt2CachedStep.Frozen.CachedBlock
