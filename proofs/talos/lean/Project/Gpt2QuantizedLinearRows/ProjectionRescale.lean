import Project.Gpt2QuantizedLinearRows.ProjectionDot
import Project.ProofKit.PackedWordAccess

namespace Project.Gpt2QuantizedLinearRows.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

def scaleCode (withBias : Bool) : Wasm.Program := ((branch withBias).drop 66).take 65

set_option maxRecDepth 32768 in
theorem scaleCode_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat) (withBias : Bool)
    (accumulator : UInt32) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input width rows).scales)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hCount : rows * outputWidth < UInt64.size) (hIndex : index < rows * outputWidth)
    (hReady : PackedGenerateLoop.Ready 29 72 73 (rows * outputWidth) index outputPtr frame)
    (hState : OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 29 72 73 (rows * outputWidth) index outputPtr result →
      OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
        width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (rescale accumulator (word (quantizeRows input width rows).scales (index / outputWidth))
          (LeanExe.Packed.getUInt32LE! weights (scaleOffset + index % outputWidth * 4))).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (scaleCode withBias ++ rest) Q initial
      { frame with values := [.i64 accumulator.toUInt64,
        .i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr,
    hValueSize, hScaleCopyOwner, hScalePtr, hScaleLength, hBytes, hTyped⟩
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
  have hOutNe : UInt64.ofNat outputWidth ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hOut64] at this
    change outputWidth = 0 at this
    omega
  have hDiv := (UInt64.ofNat_div (hIndex.trans hCount) hOut64).symm
  have hMod := (UInt64.ofNat_mod (hIndex.trans hCount) hOut64).symm
  have hRow : index / outputWidth < rows := (Nat.div_lt_iff_lt_mul hOut).mpr hIndex
  have hBound := scale_index_bound scaleOffset outputWidth index weights.size hScaleSize hOut
  have hMul := CheckedNatMul.guard_of_nat_fits (index % outputWidth) 4
    (by have := hWeights.1; change _ < 18446744073709551616; omega) (by decide)
  have hAdd := CheckedNatAdd.guard_of_fits scaleOffset (index % outputWidth * 4)
    (by have := hWeights.1; change _ < 18446744073709551616; omega)
  cases withBias <;>
    simp only [scaleCode, branch, outputWord, outputBody, func8, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.take, List.drop, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
  all_goals
    wp_packed_frame [hParams, hLength, hCounter, hScaleCopyOwner, hScalePtr, hScaleLength, hDiv, hOutNe]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hOutNe)]
    wp_packed_frame [hParams, hLength, hCounter, hScaleCopyOwner, hScalePtr, hScaleLength, hDiv, hOutNe]
    have hRead := PackedWordRead.exact «module» 0 (some 0) rfl rfl env initial scalePtr scalePtr
      (quantizeRows input width rows).scales (index / outputWidth) hScales
      (by rw [quantized_scales_size]; omega)
    simp only [quantized_scales_size] at hRead
    refine wp_call_tw (hRead.append_args rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
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
      (scaleOffset + index % outputWidth * 4) 74 75 76
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
        (word (quantizeRows input width rows).scales (index / outputWidth))
        (LeanExe.Packed.getUInt32LE! weights (scaleOffset + index % outputWidth * 4))).append_args
        rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
      rintro final values ⟨returned, rfl, hFinal, rfl⟩
      subst final
      apply Frame.of_withValues
        (P := fun result => PackedGenerateLoop.Ready 29 72 73 (rows * outputWidth) index outputPtr result ∧
          OutputState frame.params valuePtr scalePtr width outputWidth rows result)
        (R := fun result => wp «module» rest Q initial result env)
        (values := [.i64 (rescale accumulator (word (quantizeRows input width rows).scales (index / outputWidth))
          (LeanExe.Packed.getUInt32LE! weights (scaleOffset + index % outputWidth * 4))).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
      · constructor
        · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex, hLength, List.length_set,
            List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
            reduceIte, List.getElem?_set, Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
        · simp (config := { maxDischargeDepth := 64 }) only [OutputState, hParams,
            hLength, List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte,
            hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr, hValueSize,
            hScaleCopyOwner, hScalePtr, hScaleLength, hBytes, I64Values.set, hTyped, and_self]
      · intro result h
        exact hNext result h.1 (by simpa only [hParams, parameters] using h.2)

#print axioms scaleCode_spec

end Project.Gpt2QuantizedLinearRows.Projection
