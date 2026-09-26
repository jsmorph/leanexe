import Project.Gpt2QuantizedLinearRows.ProjectionState
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Gpt2QuantizedLinearRows.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def dotPrefix (withBias : Bool) : Wasm.Program := (branch withBias).take 66

set_option maxRecDepth 32768 in
theorem dotPrefix_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat) (withBias : Bool) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hValues : ByteArrayAt initial.mem valuePtr.toNat (quantizeRows input width rows).values)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hWidth : 0 < width) (hCount : rows * outputWidth < UInt64.size)
    (hIndex : index < rows * outputWidth)
    (hReady : PackedGenerateLoop.Ready 29 72 73 (rows * outputWidth) index outputPtr frame)
    (hState : OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 29 72 73 (rows * outputWidth) index outputPtr result →
      OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
        width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (dot weights (quantizeRows input width rows).values
          (weightOffset + (index % outputWidth) * width) ((index / outputWidth) * width) width).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (dotPrefix withBias ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr,
    hValueSize, hScaleCopyOwner, hScalePtr, hScaleSize, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[18]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[61]? = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth)))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[62]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  have hRows : 0 < rows := by nlinarith
  have hOut : 0 < outputWidth := by nlinarith
  have hOut64 : outputWidth < UInt64.size := by nlinarith
  have hWidth64 : width < UInt64.size := by
    have := hWeights.1
    change width < 18446744073709551616
    nlinarith
  have hIndex64 := hIndex.trans hCount
  have hOutNe : UInt64.ofNat outputWidth ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hOut64] at this
    change outputWidth = 0 at this
    omega
  have hWidthNe : UInt64.ofNat width ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hWidth64] at this
    change width = 0 at this
    omega
  have hDiv := (UInt64.ofNat_div hIndex64 hOut64).symm
  have hMod := (UInt64.ofNat_mod hIndex64 hOut64).symm
  have hWeightBound := weight_index_bound weightOffset width outputWidth index weights.size hWeightSize hOut
  have hValueBound := input_index_bound width outputWidth rows index hIndex
  have hValueFit := hValues.1
  rw [quantized_values_size] at hValueFit
  have hColumnFit : index % outputWidth * width < UInt64.size := by
    have := hWeights.1
    change _ < 18446744073709551616
    omega
  have hRowFit : index / outputWidth * width < UInt64.size := by
    change _ < 18446744073709551616
    omega
  have hColumnGuard := CheckedNatMul.guard_of_nat_fits _ _ hColumnFit hWidthNe
  have hRowGuard := CheckedNatMul.guard_of_nat_fits _ _ hRowFit hWidthNe
  have hAdd := CheckedNatAdd.guard_of_fits weightOffset (index % outputWidth * width)
    (by have := hWeights.1; change _ < 18446744073709551616; omega)
  cases withBias <;>
    simp only [dotPrefix, branch, outputWord, outputBody, func8, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.take, List.drop, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
  all_goals
    repeat' first
      | wp_packed_frame [hParams, hLength, hCounter, hValueCopyOwner, hValuePtr, hValueSize,
          hDiv, hMod, hOutNe, hWidthNe, ← UInt64.ofNat_mul, ← UInt64.ofNat_add,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hOutNe)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hWidthNe)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hColumnGuard)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hRowGuard)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa [UInt64.ofNat_add] using hAdd)])
    have hDot := Project.Gpt2QuantizedLinearRows.dot_exact env initial 0 weightsPtr valuePtr valuePtr
      weights (quantizeRows input width rows).values
      (weightOffset + (index % outputWidth) * width) ((index / outputWidth) * width) width
      hWeights hValues hWeightBound (by rw [quantized_values_size]; exact hValueBound)
    simp only [quantized_values_size] at hDot
    refine wp_call_tw (hDot.append_args rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
    rintro final values ⟨returned, rfl, hFinal, rfl⟩
    subst final
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 29 72 73 (rows * outputWidth) index outputPtr result ∧
        OutputState frame.params valuePtr scalePtr width outputWidth rows result)
      (R := fun result => wp «module» rest Q initial result env)
      (values := [.i64 (dot weights (quantizeRows input width rows).values
        (weightOffset + (index % outputWidth) * width) ((index / outputWidth) * width) width).toUInt64,
        .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
    · constructor
      · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex, hLength, List.length_set,
          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
          reduceIte, List.getElem?_set, Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
      · simp (config := { maxDischargeDepth := 64 }) only [OutputState, parameters, hParams,
          hLength, List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte,
          hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr, hValueSize,
          hScaleCopyOwner, hScalePtr, hScaleSize, hBytes, I64Values.set, hTyped, and_self]
    · intro result h
      exact hNext result h.1 (by simpa only [hParams, parameters] using h.2)

#print axioms dotPrefix_spec

end Project.Gpt2QuantizedLinearRows.Projection
