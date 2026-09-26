import Project.Gpt2QuantizedGroupedRows.ProjectionGroup
import Project.ProofKit.F32Add

namespace Project.Gpt2QuantizedGroupedRows.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def biasCode : Wasm.Program := (branch true).drop 14

set_option maxRecDepth 32768 in
theorem biasCode_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat)
    (scaled : UInt32) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hBiasSize : biasOffset + outputWidth * 4 ≤ weights.size)
    (hCount : rows * outputWidth < UInt64.size) (hIndex : index < rows * outputWidth)
    (hReady : PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr frame)
    (hState : OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows true) valuePtr scalePtr width outputWidth rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result →
      OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
        width outputWidth rows true) valuePtr scalePtr width outputWidth rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (LeanExe.Float32.addBits scaled
          (LeanExe.Packed.getUInt32LE! weights (biasOffset + index % outputWidth * 4))).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (biasCode ++ rest) Q initial
      { frame with values := [.i64 scaled.toUInt64,
        .i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hGroups, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr,
    hValueSize, hScaleCopyOwner, hScalePtr, hScaleLength, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[19]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[82]? = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth)))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[83]? = some (.i64 outputPtr) := by
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
  have hMod := (UInt64.ofNat_mod (hIndex.trans hCount) hOut64).symm
  have hBound : biasOffset + index % outputWidth * 4 + 4 ≤ weights.size := by
    have := Nat.mod_lt index hOut
    omega
  have hMul := CheckedNatMul.guard_of_nat_fits (index % outputWidth) 4
    (by have := hWeights.1; change _ < 18446744073709551616; omega) (by decide)
  have hAdd := CheckedNatAdd.guard_of_fits biasOffset (index % outputWidth * 4)
    (by have := hWeights.1; change _ < 18446744073709551616; omega)
  simp only [biasCode, branch, outputWord, outputBody, func8, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.take, List.drop, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, ↓reduceIte, List.cons_append, List.nil_append]
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
    (biasOffset + index % outputWidth * 4) 95 96 97
    [.f32 scaled, .i32 (PackedGenerateLoop.address outputPtr index)] hWeights hBound ?_ ?_ ?_ ?_ Q _ ?_
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
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result ∧
        OutputState frame.params valuePtr scalePtr width outputWidth rows result)
      (R := fun result => wp «module» rest Q initial result env)
      (values := [.i64 (LeanExe.Float32.addBits scaled
        (LeanExe.Packed.getUInt32LE! weights (biasOffset + index % outputWidth * 4))).toUInt64,
        .i32 (PackedGenerateLoop.address outputPtr index)]) (by rw [F32Add.add_eq])
    · constructor
      · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex, hLength, List.length_set,
          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
          reduceIte, List.getElem?_set, Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
      · simp (config := { maxDischargeDepth := 64 }) only [OutputState, hParams,
          hLength, List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte,
          hGroups, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr, hValueSize,
          hScaleCopyOwner, hScalePtr, hScaleLength, hBytes, I64Values.set, hTyped, and_self]
    · intro result h
      exact hNext result h.1 (by simpa only [hParams, parameters] using h.2)

#print axioms biasCode_spec

end Project.Gpt2QuantizedGroupedRows.Projection
