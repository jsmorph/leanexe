import Project.Gpt2QuantizedCached.GroupedProjection.ProjectionGroups

namespace Project.Gpt2QuantizedCached.GroupedProjection.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def totalCode (withBias : Bool) : Wasm.Program := ((branch withBias).drop 13).take 3

set_option maxRecDepth 32768 in
theorem totalCode_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat)
    (withBias : Bool) (frame : Locals)
    (hReady : PackedGenerateLoop.Ready 32 95 96 (rows * outputWidth) index outputPtr frame)
    (hAcc : Accumulator weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
      biasOffset width outputWidth rows index (width / 64) withBias frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 32 95 96 (rows * outputWidth) index outputPtr result →
      OutputState (parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset scaleOffset biasOffset
        width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (sumPrefix weights input weightOffset scaleOffset width rows
          (index / outputWidth) (index % outputWidth) (width / 64)).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (totalCode withBias ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hAcc with ⟨hState, hTotal, _⟩
  have hParams := hState.1
  have hLength := hState.2.1
  rcases hState with ⟨_, _, hGroups, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr,
    hValueSize, hScaleCopyOwner, hScalePtr, hScaleLength, hBytes, hTyped⟩
  have hCounter : frame.locals[19]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, parameters, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[82]? = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth)))) := by
    simpa [Locals.get, hParams, parameters, hLength] using hReady.2.2.1
  have hPointer : frame.locals[83]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, parameters, hLength] using hReady.2.2.2.1
  cases withBias <;>
    simp only [totalCode, branch, outputWord, outputBody, func8, Project.Gpt2QuantizedCached.func42,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hTotal
    wp_packed_frame [hParams, parameters, hLength, hTotal]
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 32 95 96 (rows * outputWidth) index outputPtr result ∧
        OutputState frame.params valuePtr scalePtr width outputWidth rows result)
      (R := fun result => wp «module» rest Q initial result env) rfl
    · constructor
      · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex, hParams, parameters,
          hLength, List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
          Nat.reduceSub, reduceIte, List.getElem?_set, Nat.reduceEqDiff,
          hCounter, hLengthLocal, hPointer, true_and]
      · simp only [OutputState, hParams, parameters, hLength, List.length_set, List.getElem?_set,
          Nat.reduceEqDiff, Nat.reduceLT, Bool.false_eq_true, reduceIte, hGroups,
          hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr, hValueSize,
          hScaleCopyOwner, hScalePtr, hScaleLength, hBytes, I64Values.set, hTyped, and_self]
    · intro result h
      exact hNext result h.1 (by simpa only [hParams] using h.2)

#print axioms totalCode_spec

end Project.Gpt2QuantizedCached.GroupedProjection.Projection
