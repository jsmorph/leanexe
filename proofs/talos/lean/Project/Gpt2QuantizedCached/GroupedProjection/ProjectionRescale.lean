import Project.Gpt2QuantizedCached.GroupedProjection.ProjectionDot
import Project.ProofKit.PackedWordAccess

namespace Project.Gpt2QuantizedCached.GroupedProjection.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

def scaleCode (withBias : Bool) : Wasm.Program := ((groupStep withBias).drop 104).take 84

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1600000 in
theorem scaleCode_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index group : Nat) (withBias : Bool)
    (accumulator : UInt32) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input 64 (rows * (width / 64))).scales)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hCount : rows * outputWidth < UInt64.size) (hIndex : index < rows * outputWidth)
    (hGroup : group < width / 64)
    (hReady : PackedGenerateLoop.Ready 32 95 96 (rows * outputWidth) index outputPtr frame)
    (hGroupReady : RangeFoldLoop.Ready 97 98 (width / 64) group frame)
    (hState : StepState weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
      biasOffset width outputWidth rows index group withBias frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 32 95 96 (rows * outputWidth) index outputPtr result →
      RangeFoldLoop.Ready 97 98 (width / 64) group result →
      StepState weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
        biasOffset width outputWidth rows index group withBias result →
      wp «module» rest Q initial { result with values :=
        [.i64 (rescale accumulator
          (word (quantizeRows input 64 (rows * (width / 64))).scales (index / outputWidth * (width / 64) + group))
          (LeanExe.Packed.getUInt32LE! weights (scaleOffset + index % outputWidth * 4))).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (scaleCode withBias ++ rest) Q initial
      { frame with values := [.i64 accumulator.toUInt64,
        .i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨⟨hState, hTotal, hStride⟩, hGroupCopy, hTotalCopy⟩
  rcases hState with ⟨hParams, hLength, hGroups, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr,
    hValueSize, hScaleCopyOwner, hScalePtr, hScaleLength, hBytes, hTyped⟩
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
  have hRows : 0 < rows := by nlinarith
  have hOut : 0 < outputWidth := by nlinarith
  have hOut64 : outputWidth < UInt64.size := by nlinarith
  have hOutNe : UInt64.ofNat outputWidth ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hOut64] at this
    change outputWidth = 0 at this
    omega
  have hDiv := (UInt64.ofNat_div (hIndex.trans hCount) hOut64).symm
  have hMod := (UInt64.ofNat_mod (hIndex.trans hCount) hOut64).symm
  have hRow : index / outputWidth < rows := (Nat.div_lt_iff_lt_mul hOut).mpr hIndex
  have hScaleFit := hScales.1
  rw [Project.Gpt2QuantizedLinearRows.quantized_scales_size] at hScaleFit
  have hGroups64 : width / 64 < UInt64.size := by
    change _ < 18446744073709551616
    nlinarith
  have hGroupsNe : UInt64.ofNat (width / 64) ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hGroups64] at this
    change width / 64 = 0 at this
    omega
  have hScaleIndex : index / outputWidth * (width / 64) + group < rows * (width / 64) := by
    have := Nat.mul_le_mul_right (width / 64) (Nat.succ_le_of_lt hRow)
    nlinarith
  have hRowMul := CheckedNatMul.guard_of_nat_fits (index / outputWidth) (width / 64)
    (by change _ < 18446744073709551616; omega) hGroupsNe
  have hRowAdd := CheckedNatAdd.guard_of_fits (index / outputWidth * (width / 64)) group
    (by change _ < 18446744073709551616; omega)
  have hBound : scaleOffset + index % outputWidth * 4 + 4 ≤ weights.size := by
    have := Nat.mod_lt index hOut
    omega
  have hMul := CheckedNatMul.guard_of_nat_fits (index % outputWidth) 4
    (by have := hWeights.1; change _ < 18446744073709551616; omega) (by decide)
  have hAdd := CheckedNatAdd.guard_of_fits scaleOffset (index % outputWidth * 4)
    (by have := hWeights.1; change _ < 18446744073709551616; omega)
  cases withBias <;>
    simp only [scaleCode, groupStep, groupBody, branch, outputWord, outputBody, func8, Project.Gpt2QuantizedCached.func42,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hTotal hGroupCopy hTotalCopy
    repeat' first
      | wp_packed_frame [hParams, hLength, hCounter, hGroups, hGroupCopy, hScaleCopyOwner,
          hScalePtr, hScaleLength, hDiv, hOutNe, hGroupsNe, ← UInt64.ofNat_mul, ← UInt64.ofNat_add,
          List.getElem?_cons_zero, List.getElem?_cons_succ]
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hOutNe)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hGroupsNe)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hRowMul)])
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa [UInt64.ofNat_add] using hRowAdd)])
    have hRead := PackedWordRead.exact «module» 31 (some 31) rfl rfl env initial scalePtr scalePtr
      (quantizeRows input 64 (rows * (width / 64))).scales
      (index / outputWidth * (width / 64) + group) hScales
      (by rw [Project.Gpt2QuantizedLinearRows.quantized_scales_size]; omega)
    simp only [Project.Gpt2QuantizedLinearRows.quantized_scales_size] at hRead
    refine wp_call_tw (by simpa only [UInt64.ofNat_add, UInt64.ofNat_mul, List.cons_append, List.nil_append] using
      (hRead.append_args rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)])) ?_
    rintro final values ⟨returned, rfl, hFinal, rfl⟩
    subst final
    wp_packed_frame [hParams, hLength, hCounter]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hOutNe)]
    wp_packed_frame [hParams, hLength, hCounter, hMod, hOutNe]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame [hParams, hLength, hCounter, hMod]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hMul)]
    wp_packed_frame [hParams, hLength, hCounter, hMod, ← UInt64.ofNat_mul]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hAdd)]
    wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_add]
    refine PackedWordAccess.guard_spec «module» env initial _ weightsPtr weights
      (scaleOffset + index % outputWidth * 4) 100 101 102
      [.i32 (PackedGenerateLoop.address outputPtr index)] hWeights hBound ?_ ?_ ?_ ?_ Q _ ?_
    · simp only [Locals.get, hParams, hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set, Nat.reduceEqDiff]
    · simp only [Locals.get, hParams, hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set, Nat.reduceEqDiff]
    · simp only [Locals.get, hParams, hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set, Nat.reduceEqDiff,
        UInt64.ofNat_add, UInt64.ofNat_mul]
      rfl
    · simp only [UInt64.ofNat_add, UInt64.ofNat_mul]; rfl
    · wp_packed_frame [hParams, hLength]
      refine wp_call_tw ((rescale_exact env initial accumulator
        (word (quantizeRows input 64 (rows * (width / 64))).scales
          (index / outputWidth * (width / 64) + group))
        (LeanExe.Packed.getUInt32LE! weights (scaleOffset + index % outputWidth * 4))).append_args
        rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
      rintro final values ⟨returned, rfl, hFinal, rfl⟩
      subst final
      apply Frame.of_withValues
        (P := fun result => PackedGenerateLoop.Ready 32 95 96 (rows * outputWidth) index outputPtr result ∧
          RangeFoldLoop.Ready 97 98 (width / 64) group result ∧
          StepState weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
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
              hScaleCopyOwner, hScalePtr, hScaleLength, hBytes, I64Values.set, hTyped,
              hTotal, hStride, hGroupCopy, hTotalCopy, and_self, true_and]

#print axioms scaleCode_spec

end Project.Gpt2QuantizedCached.GroupedProjection.Projection
