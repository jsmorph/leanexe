import Project.Gpt2QuantizedCached.CachedBlock.Base
import Project.Gpt2QuantizedCached.LayerNorm

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def parameters (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position : Nat) : List Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
   .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size),
   .i64 cacheOwner, .i64 cachePtr, .i64 (UInt64.ofNat cache.size),
   .i64 (UInt64.ofNat layer), .i64 (UInt64.ofNat position)]

def NormalizedState (params : List Value) (base : Nat) (outputPtr : UInt64) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 193 ∧ frame.values = [] ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat base)) ∧
  frame.locals[10]? = some (.i64 outputPtr) ∧ frame.locals[11]? = some (.i64 outputPtr) ∧
  frame.locals[12]? = some (.i64 3072) ∧ frame.locals[13]? = some (.i64 outputPtr) ∧
  frame.locals[14]? = some (.i64 outputPtr) ∧ frame.locals[15]? = some (.i64 3072) ∧
  I64Values frame.locals

def normalizedCode : Wasm.Program :=
  [
  .localGet 0,
  .localSet 12,
  .localGet 1,
  .localSet 13,
  .localGet 2,
  .localSet 14,
  .localGet 3,
  .localSet 15,
  .localGet 4,
  .localSet 16,
  .localGet 5,
  .localSet 17,
  .localGet 11,
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
  .localSet 18,
  .localGet 11,
  .localSet 199,
  .constI64 4,
  .localSet 200,
  .localGet 200,
  .constI64 0,
  .eqI64,
  .iff 0 1 [
   .constI64 0
  ] [
   .localGet 199,
   .localGet 200,
   .divUI64
  ] [] [.i64],
  .localSet 196,
  .constI64 768,
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
  .localSet 19,
  .constI64 1,
  .localSet 20,
  .localGet 12,
  .localGet 13,
  .localGet 14,
  .localGet 15,
  .localGet 16,
  .localGet 17,
  .localGet 18,
  .localGet 19,
  .localGet 20,
  .call 34,
  .localSet 23,
  .localSet 22,
  .localSet 21,
  .localGet 21,
  .localSet 24,
  .localGet 22,
  .localSet 25,
  .localGet 23,
  .localSet 26
  ]

set_option maxRecDepth 32768 in
theorem emitted_normalized : (func54.drop 19).take 61 = normalizedCode := rfl

theorem normalized_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position base : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hInputSize : 3072 ≤ input.size) (hWeightsSize : (base / 4 + 1536) * 4 ≤ weights.size)
    (hResources : Gpt2CachedStep.LayerNorm.Resources heap 1 (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 193) (hValues : frame.values = [])
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat base))) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      NormalizedState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) base (Gpt2CachedStep.LayerNorm.outputNode heap 1).root result →
      (Gpt2CachedStep.LayerNorm.finalHeap heap 1).At final →
      (Gpt2CachedStep.LayerNorm.finalHeap heap 1).OwnsPacked final (Gpt2CachedStep.LayerNorm.outputNode heap 1)
        (layerNorm weights input (base / 4) (base / 4 + 768) 1) →
      heap.Frame initial (Gpt2CachedStep.LayerNorm.finalHeap heap 1) final →
      final.mem.pages ≤ 65536 → final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0 →
      wp «module» rest Q final result env) :
    wp «module» ((func54.drop 19).take 61 ++ rest) Q initial frame env := by
  have hScaleSize : (base / 4 + 768) * 4 ≤ weights.size :=
    (Nat.mul_le_mul_right 4 (Nat.add_le_add_left (by decide : 768 ≤ 1536) (base / 4))).trans hWeightsSize
  have hBiasSize : (base / 4 + 768 + 768) * 4 ≤ weights.size := by
    rw [Nat.add_assoc]
    exact hWeightsSize
  have hBaseFit : base / 4 + 768 < UInt64.size := by
    have := hWeights.1
    change base / 4 + 768 < 18446744073709551616
    omega
  have hAddSafe := CheckedNatAdd.guard_of_fits (base / 4) 768 hBaseFit
  have hAdd : UInt64.ofNat (base / 4) + 768 = UInt64.ofNat (base / 4 + 768) := by simp
  simp only [show UInt64.ofNat 768 = 768 from rfl] at hAddSafe
  have hBase64 : base < UInt64.size := by
    have := hWeights.1
    change base < 18446744073709551616
    omega
  have hDiv : UInt64.ofNat base / 4 = UInt64.ofNat (base / 4) :=
    (UInt64.ofNat_div hBase64 (by decide)).symm
  rw [emitted_normalized]
  simp only [normalizedCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hBase]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, parameters, hLocals, hDiv, hBase]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, parameters, hLocals, hDiv, hBase]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAddSafe)]
  wp_packed_frame [hParams, parameters, hLocals, hAdd]
  refine wp_call_tw (LayerNorm.layerNorm_exact env initial heap
    weightsOwner inputOwner weightsPtr inputPtr weights input (base / 4) (base / 4 + 768) 1
    hHeap hWeights hInput hWeightsProtected hInputProtected hInputSize hScaleSize hBiasSize
    hResources hPages) ?_
  rintro final values ⟨hReturned, hFinalHeap, hOutput, hFrame, hFinalPages, hCapacity⟩
  rw [Gpt2CachedStep.LayerNorm.layerNorm_size] at hReturned
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

end Project.Gpt2QuantizedCached.CachedBlock
