import Project.Gpt2CachedStep.CachedBlock.FrozenBase
import Project.Gpt2CachedStep.LayerNorm.FrozenSpec

namespace Project.Gpt2CachedStep.Frozen.CachedBlock
open Wasm Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def parameters (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position : Nat) : List Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
   .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size),
   .i64 cacheOwner, .i64 cachePtr, .i64 (UInt64.ofNat cache.size),
   .i64 (UInt64.ofNat layer), .i64 (UInt64.ofNat position)]

def NormalizedState (params : List Value) (base : Nat) (outputPtr : UInt64) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 164 ∧ frame.values = [] ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat base)) ∧
  frame.locals[10]? = some (.i64 outputPtr) ∧ frame.locals[11]? = some (.i64 outputPtr) ∧
  frame.locals[12]? = some (.i64 3072) ∧ frame.locals[13]? = some (.i64 outputPtr) ∧
  frame.locals[14]? = some (.i64 outputPtr) ∧ frame.locals[15]? = some (.i64 3072) ∧
  I64Values frame.locals

def normalizedCode : Wasm.Program :=
  [.localGet 0, .localSet 12, .localGet 1, .localSet 13, .localGet 2, .localSet 14,
   .localGet 3, .localSet 15, .localGet 4, .localSet 16, .localGet 5, .localSet 17,
   .localGet 11, .localSet 18, .localGet 11, .localSet 167, .constI64 768, .localSet 168,
   .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 19,
   .constI64 1, .localSet 20,
   .localGet 12, .localGet 13, .localGet 14, .localGet 15, .localGet 16, .localGet 17,
   .localGet 18, .localGet 19, .localGet 20, .call 20,
   .localSet 23, .localSet 22, .localSet 21,
   .localGet 21, .localSet 24, .localGet 22, .localSet 25, .localGet 23, .localSet 26]

set_option maxRecDepth 32768 in
theorem emitted_normalized : (func33.drop 19).take 47 = normalizedCode := rfl

theorem normalized_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hInputSize : 3072 ≤ input.size) (hWeightsSize : (base + 1536) * 4 ≤ weights.size)
    (hResources : LayerNorm.Resources heap 1 (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      NormalizedState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) base (LayerNorm.outputNode heap 1).root result →
      (LayerNorm.finalHeap heap 1).At final →
      (LayerNorm.finalHeap heap 1).OwnsPacked final (LayerNorm.outputNode heap 1)
        (layerNorm weights input base (base + 768) 1) →
      heap.Frame initial (LayerNorm.finalHeap heap 1) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func33.drop 19).take 47 ++ rest) Q initial frame env := by
  have hScaleSize : (base + 768) * 4 ≤ weights.size :=
    (Nat.mul_le_mul_right 4 (Nat.add_le_add_left (by decide : 768 ≤ 1536) base)).trans hWeightsSize
  have hBiasSize : (base + 768 + 768) * 4 ≤ weights.size := by
    rw [Nat.add_assoc]
    exact hWeightsSize
  have hBaseFit : base + 768 < UInt64.size := by
    have := hWeights.1
    change base + 768 < 18446744073709551616
    omega
  have hAddSafe := CheckedNatAdd.guard_of_fits base 768 hBaseFit
  have hAdd : UInt64.ofNat base + 768 = UInt64.ofNat (base + 768) := by simp
  simp only [show UInt64.ofNat 768 = 768 from rfl] at hAddSafe
  rw [emitted_normalized]
  simp only [normalizedCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAddSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hAdd]
  refine wp_call_tw (LayerNorm.Spec.layerNorm_exact env initial heap
    weightsOwner inputOwner weightsPtr inputPtr weights input base (base + 768) 1
    hHeap hWeights hInput hWeightsProtected hInputProtected hInputSize hScaleSize hBiasSize
    hResources hPages) ?_
  rintro final values ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  rw [LayerNorm.layerNorm_size] at hReturned
  subst values
  wp_packed_frame [hParams, parameters, hLocals]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [NormalizedState, parameters, hLocals, List.length_set,
      List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte, hBase,
      I64Values.set, hTyped, show UInt64.ofNat (4 * (1 * 768)) = 3072 from rfl, and_self]
  · exact hFinalHeap
  · exact hOutput
  · exact hFrame
  · exact hFinalPages
  · exact hCapacity

#print axioms normalized_spec

end Project.Gpt2CachedStep.Frozen.CachedBlock
