import Project.Gpt2CachedStep.CachedBlock.Normalized
import Project.Gpt2CachedStep.LinearRows.Heap

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def qkvNeed : UInt64 := PackedCapacity.capacity 9216

def QkvState (params : List Value) (base : Nat) (normalizedPtr qkvPtr : UInt64) (frame : Locals) : Prop :=
  NormalizedState params base normalizedPtr frame ∧
  frame.locals[27]? = some (.i64 qkvPtr) ∧ frame.locals[28]? = some (.i64 qkvPtr) ∧
  frame.locals[29]? = some (.i64 9216) ∧ frame.locals[30]? = some (.i64 qkvPtr) ∧
  frame.locals[31]? = some (.i64 qkvPtr) ∧ frame.locals[32]? = some (.i64 9216)

def qkvCode : Wasm.Program :=
  [.localGet 0, .localSet 27, .localGet 1, .localSet 28, .localGet 2, .localSet 29,
   .localGet 24, .localSet 30, .localGet 25, .localSet 31, .localGet 26, .localSet 32,
   .localGet 11, .localSet 167, .constI64 1536, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 33,
   .localGet 11, .localSet 167, .call 4, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 34,
   .constI64 768, .localSet 35, .constI64 2304, .localSet 36, .constI64 1, .localSet 37,
   .localGet 27, .localGet 28, .localGet 29, .localGet 30, .localGet 31, .localGet 32,
   .localGet 33, .localGet 34, .localGet 35, .localGet 36, .localGet 37, .call 21,
   .localSet 40, .localSet 39, .localSet 38,
   .localGet 38, .localSet 41, .localGet 39, .localSet 42, .localGet 40, .localSet 43]

set_option maxRecDepth 32768 in
theorem emitted_qkv : (func33.drop 66).take 63 = qkvCode := rfl

theorem qkv_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr normalizedPtr : UInt64)
    (weights input cache normalized : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hNormalized : ByteArrayAt initial.mem normalizedPtr.toNat normalized)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hNormalizedProtected : heap.Protects normalizedPtr.toNat (normalizedPtr.toNat + normalized.size))
    (hNormalizedSize : normalized.size = 3072)
    (hWeightsSize : (base + qkvBiasOffset + 2304) * 4 ≤ weights.size)
    (hResources : LayerNorm.AllocationFits heap qkvNeed (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : NormalizedState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position) base normalizedPtr frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      QkvState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) base normalizedPtr (allocatedNode heap.top qkvNeed heap.nodes).root result →
      (heap.allocate qkvNeed).At final →
      (heap.allocate qkvNeed).OwnsPacked final (allocatedNode heap.top qkvNeed heap.nodes)
        (linearRows weights normalized (base + qkvWeightOffset) (base + qkvBiasOffset) 768 2304 1) →
      heap.Frame initial (heap.allocate qkvNeed) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 66).take 63 ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hBase, hNormalizedOwner, hNormalizedPtr,
    hNormalizedBytes, hCopiedOwner, hCopiedPtr, hCopiedBytes, hTyped⟩
  have hMatrixSize : (base + qkvWeightOffset + 768 * 2304) * 4 ≤ weights.size := by
    rw [Nat.add_assoc]
    exact (Nat.mul_le_mul_right 4 (Nat.le_add_right (base + qkvBiasOffset) 2304)).trans hWeightsSize
  have hWeightFit : base + qkvWeightOffset < UInt64.size := by
    have := hWeights.1
    change base + 1536 < 18446744073709551616
    change (base + 1771008 + 2304) * 4 ≤ weights.size at hWeightsSize
    omega
  have hBiasFit : base + qkvBiasOffset < UInt64.size := by
    have := hWeights.1
    change base + 1771008 < 18446744073709551616
    change (base + 1771008 + 2304) * 4 ≤ weights.size at hWeightsSize
    omega
  have hWeightSafe := CheckedNatAdd.guard_of_fits base qkvWeightOffset hWeightFit
  have hBiasSafe := CheckedNatAdd.guard_of_fits base qkvBiasOffset hBiasFit
  have hWeightAdd : UInt64.ofNat base + 1536 = UInt64.ofNat (base + qkvWeightOffset) := by
    change UInt64.ofNat base + UInt64.ofNat qkvWeightOffset = _
    exact (UInt64.ofNat_add _ _).symm
  have hBiasAdd : UInt64.ofNat base + UInt64.ofNat qkvBiasOffset = UInt64.ofNat (base + qkvBiasOffset) :=
    (UInt64.ofNat_add _ _).symm
  simp only [show UInt64.ofNat qkvWeightOffset = 1536 from rfl] at hWeightSafe
  have hCall := LinearRows.Spec.linearRows_owned env initial heap weightsOwner normalizedPtr
    weightsPtr normalizedPtr weights normalized (base + qkvWeightOffset) (base + qkvBiasOffset) 768 2304 1
    hHeap hWeights hNormalized (by rw [hNormalizedSize]) hMatrixSize hWeightsSize
    (by decide) (by decide) (by decide) hResources hPages hWeightsProtected hNormalizedProtected
  simp only [hNormalizedSize] at hCall
  rw [emitted_qkv]
  simp only [qkvCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase, hCopiedOwner, hCopiedPtr, hCopiedBytes]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hWeightSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hBase, hWeightAdd]
  refine wp_call_tw (Layout.qkvBiasOffset_exact env initial) ?_
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
  · simp (config := { maxDischargeDepth := 64 }) only [QkvState, NormalizedState, parameters, qkvNeed, hLocals,
      List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, hBase,
      hNormalizedOwner, hNormalizedPtr, hNormalizedBytes, hCopiedOwner, hCopiedPtr, hCopiedBytes,
      I64Values.set, hTyped, show UInt64.ofNat (4 * (1 * 2304)) = 9216 from rfl, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms qkv_spec

end Project.Gpt2CachedStep.CachedBlock
