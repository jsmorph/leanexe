import Project.Gpt2QuantizedGroupedRows.ProjectionState
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Gpt2QuantizedGroupedRows.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def dotPrefix (withBias : Bool) : Wasm.Program := (groupStep withBias).take 104

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1600000 in
theorem dotPrefix_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index group : Nat)
    (withBias : Bool) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hValues : ByteArrayAt initial.mem valuePtr.toNat (quantizeRows input 64 (rows * (width / 64))).values)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hWidth : 0 < width) (hMultiple : 64 ∣ width) (hCount : rows * outputWidth < UInt64.size)
    (hIndex : index < rows * outputWidth) (hGroup : group < width / 64)
    (hReady : PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr frame)
    (hGroupReady : RangeFoldLoop.Ready 95 96 (width / 64) group frame)
    (hAcc : Accumulator weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
      biasOffset width outputWidth rows index group withBias frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result →
      RangeFoldLoop.Ready 95 96 (width / 64) group result →
      StepState weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
        biasOffset width outputWidth rows index group withBias result →
      wp «module» rest Q initial { result with values :=
        [.i64 (dot weights (quantizeRows input 64 (rows * (width / 64))).values
          (weightOffset + (index % outputWidth) * width + group * 64)
          ((index / outputWidth) * width + group * 64) 64).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (dotPrefix withBias ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hAcc with ⟨hState, hTotal, hStride⟩
  rcases hState with ⟨hParams, hLength, hGroups, hValueOwner, hScaleOwner, hValueCopyOwner,
    hValuePtr, hValueSize, hScaleCopyOwner, hScalePtr, hScaleSize, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[19]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[82]? = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth)))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[83]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  have hGroupCounter : frame.locals[84]? = some (.i64 (UInt64.ofNat group)) := by
    simpa [Locals.get, hParams, hLength] using hGroupReady.2.1
  have hGroupStop : frame.locals[85]? = some (.i64 (UInt64.ofNat (width / 64))) := by
    simpa [Locals.get, hParams, hLength] using hGroupReady.2.2
  have hOut : 0 < outputWidth := by nlinarith
  have hRows : 0 < rows := by nlinarith
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
  have hGroupBound : group * 64 + 64 ≤ width := by omega
  have hColumn := Nat.mod_lt index hOut
  have hRow : index / outputWidth < rows := (Nat.div_lt_iff_lt_mul hOut).mpr hIndex
  have hWeightBound : weightOffset + index % outputWidth * width + group * 64 + 64 ≤ weights.size := by
    have := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hColumn)
    nlinarith
  have hValueBound : index / outputWidth * width + group * 64 + 64 ≤ rows * width := by
    have := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hRow)
    nlinarith
  have hValueFit := hValues.1
  rw [grouped_values_size input width rows hMultiple] at hValueFit
  have hColumnFit : index % outputWidth * width < UInt64.size := by
    have := hWeights.1
    change _ < 18446744073709551616
    omega
  have hRowFit : index / outputWidth * width < UInt64.size := by
    change _ < 18446744073709551616
    omega
  have hGroupFit : group * 64 < UInt64.size := by omega
  have hColumnGuard := CheckedNatMul.guard_of_nat_fits _ _ hColumnFit hWidthNe
  have hRowGuard := CheckedNatMul.guard_of_nat_fits _ _ hRowFit hWidthNe
  have hGroupGuard := CheckedNatMul.guard_of_nat_fits _ _ hGroupFit (by decide : (64 : UInt64) ≠ 0)
  have hBaseGuard := CheckedNatAdd.guard_of_fits weightOffset (index % outputWidth * width)
    (by have := hWeights.1; change _ < 18446744073709551616; omega)
  have hWeightGuard := CheckedNatAdd.guard_of_fits (weightOffset + index % outputWidth * width) (group * 64)
    (by have := hWeights.1; change _ < 18446744073709551616; omega)
  have hInputGuard := CheckedNatAdd.guard_of_fits (index / outputWidth * width) (group * 64)
    (by change _ < 18446744073709551616; omega)
  cases withBias <;>
    simp only [dotPrefix, groupStep, groupBody, branch, outputWord, outputBody, func8,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hTotal
    repeat' first
      | wp_packed_frame [hParams, hLength, hCounter, hGroupCounter, hTotal, hValueCopyOwner,
          hValuePtr, hValueSize, hDiv, hMod, hOutNe, hWidthNe,
          ← UInt64.ofNat_mul, ← UInt64.ofNat_add,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hOutNe)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hWidthNe)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by decide)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hColumnGuard)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hRowGuard)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hGroupGuard)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa [UInt64.ofNat_add] using hBaseGuard)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa [UInt64.ofNat_add] using hWeightGuard)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa [UInt64.ofNat_add] using hInputGuard)])
    have hDot := Project.Gpt2QuantizedGroupedRows.dot_exact env initial 0 weightsPtr valuePtr valuePtr
      weights (quantizeRows input 64 (rows * (width / 64))).values
      (weightOffset + (index % outputWidth) * width + group * 64)
      ((index / outputWidth) * width + group * 64) 64 hWeights hValues hWeightBound
      (by rw [grouped_values_size input width rows hMultiple]; exact hValueBound)
    simp only [grouped_values_size input width rows hMultiple] at hDot
    refine wp_call_tw (by simpa only [UInt64.ofNat_add, UInt64.ofNat_mul, List.cons_append, List.nil_append,
      (show UInt64.ofNat 64 = 64 from rfl)] using
      (hDot.append_args rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)])) ?_
    rintro final values ⟨returned, rfl, hFinal, rfl⟩
    subst final
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result ∧
        RangeFoldLoop.Ready 95 96 (width / 64) group result ∧
        StepState weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
          biasOffset width outputWidth rows index group _ result)
      (R := fun result => wp «module» rest Q initial result env) rfl
    case hNext =>
      intro result h
      exact hNext result h.1 h.2.1 h.2.2
    · constructor
      · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex, hLength, List.length_set,
          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
          reduceIte, List.getElem?_set, Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
      · constructor
        · simp only [RangeFoldLoop.Ready, Locals.get, hLength, List.length_set,
            List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
            reduceIte, List.getElem?_set, Nat.reduceEqDiff, hGroupCounter, hGroupStop, true_and]
        · simp (config := { maxDischargeDepth := 64 }) only [StepState, Accumulator, OutputState, parameters,
            hParams, hLength, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, Bool.false_eq_true, reduceIte,
            hGroups, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr, hValueSize,
            hScaleCopyOwner, hScalePtr, hScaleSize, hBytes, I64Values.set, hTyped, hTotal, hStride, and_self, true_and]

#print axioms dotPrefix_spec

end Project.Gpt2QuantizedGroupedRows.Projection
