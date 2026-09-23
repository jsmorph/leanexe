import Project.Gpt2QuantizedGroupedRows.ProjectionRescale
import Project.ProofKit.F32Add

namespace Project.Gpt2QuantizedGroupedRows.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def finishGroup (withBias : Bool) : Wasm.Program := (groupStep withBias).drop 188

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1600000 in
theorem finishGroup_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index group : Nat)
    (withBias : Bool) (frame : Locals)
    (hGroups64 : width / 64 < UInt64.size) (hGroup : group < width / 64)
    (hReady : PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr frame)
    (hGroupReady : RangeFoldLoop.Ready 95 96 (width / 64) group frame)
    (hState : StepState weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
      biasOffset width outputWidth rows index group withBias frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result →
      RangeFoldLoop.Ready 95 96 (width / 64) (group + 1) result →
      Accumulator weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
        biasOffset width outputWidth rows index (group + 1) withBias result →
      wp «module» rest Q initial { result with values :=
        [.i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (finishGroup withBias ++ rest) Q initial
      { frame with values := [.i64
        (partialValue weights input weightOffset scaleOffset width rows
          (index / outputWidth) (index % outputWidth) group).toUInt64,
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
  have hIncrement := CheckedNatAdd.guard_of_fits group 1 (by omega)
  cases withBias <;>
    simp only [finishGroup, groupStep, groupBody, branch, outputWord, outputBody, func8,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hTotal hGroupCopy hTotalCopy
    wp_packed_frame [hParams, hLength, hTotalCopy, hGroupCounter, hStride,
      List.getElem?_cons_zero, List.getElem?_cons_succ]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hIncrement)]
    wp_packed_frame [hParams, hLength]
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result ∧
        RangeFoldLoop.Ready 95 96 (width / 64) (group + 1) result ∧
        Accumulator weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
          biasOffset width outputWidth rows index (group + 1) _ result)
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
            reduceIte, List.getElem?_set, Nat.reduceEqDiff, hGroupStop, UInt64.ofNat_add, true_and]
          exact ⟨rfl, trivial⟩
        · simp (config := { maxDischargeDepth := 64 }) only [Accumulator, OutputState, parameters,
            hParams, hLength, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT,
            Bool.false_eq_true, reduceIte, hGroups, hValueOwner, hScaleOwner, hValueCopyOwner,
            hValuePtr, hValueSize, hScaleCopyOwner, hScalePtr, hScaleLength, hBytes,
            I64Values.set, hTyped, hStride, sumPrefix_succ, F32Add.add_eq, and_self, true_and]

#print axioms finishGroup_spec

end Project.Gpt2QuantizedGroupedRows.Projection
