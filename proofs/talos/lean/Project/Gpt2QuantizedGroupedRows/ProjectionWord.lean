import Project.Gpt2QuantizedGroupedRows.ProjectionBias
import Project.Gpt2QuantizedGroupedRows.ProjectionTotal

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedGroupedRows.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

theorem branch_parts (withBias : Bool) :
    branch withBias = groupsCode withBias ++ totalCode withBias ++
      if withBias then biasCode else [.localSet 88, .localGet 88] := by
  cases withBias <;> rfl

theorem branch_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat) (withBias : Bool) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hValues : ByteArrayAt initial.mem valuePtr.toNat (quantizeRows input 64 (rows * (width / 64))).values)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input 64 (rows * (width / 64))).scales)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hBiasSize : withBias = true → biasOffset + outputWidth * 4 ≤ weights.size)
    (hWidth : 0 < width) (hMultiple : 64 ∣ width) (hCount : rows * outputWidth < UInt64.size) (hIndex : index < rows * outputWidth)
    (hReady : PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr frame)
    (hState : OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result →
      OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
        width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (value weights input weightOffset scaleOffset biasOffset width outputWidth rows index withBias).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (branch withBias ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rw [branch_parts, List.append_assoc, List.append_assoc]
  apply groupsCode_spec env initial weightsPtr inputPtr valuePtr scalePtr outputPtr weights input
    weightOffset scaleOffset biasOffset width outputWidth rows index withBias frame
    hWeights hValues hScales hWeightSize hScaleSize hWidth hMultiple hCount hIndex hReady hState
  intro afterGroups hReadyGroups hAccGroups
  apply totalCode_spec env initial weightsPtr inputPtr valuePtr scalePtr outputPtr weights input
    weightOffset scaleOffset biasOffset width outputWidth rows index withBias afterGroups
    hReadyGroups hAccGroups
  intro afterScale hReadyScale hStateScale
  cases withBias with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
    have hParams := hStateScale.1
    have hLength := hStateScale.2.1
    have hTyped : I64Values afterScale.locals := by
      rcases hStateScale with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h⟩
      exact h
    wp_packed_frame [hParams, parameters, hLength]
    let scaled := value weights input weightOffset scaleOffset biasOffset width outputWidth rows index false
    let result := { afterScale with locals := afterScale.locals.set 77 (.i64 scaled.toUInt64) }
    have hReadyResult : PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result := by
      simpa only [result, PackedGenerateLoop.Ready, Locals.get, Locals.validIndex, hParams, parameters,
        hLength, List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, reduceIte, List.getElem?_set, Nat.reduceEqDiff] using hReadyScale
    have hStateResult : OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
        width outputWidth rows false) valuePtr scalePtr width outputWidth rows result := by
      simpa only [result, OutputState, hParams, parameters, hLength, List.length_set, List.getElem?_set,
        Nat.reduceEqDiff, reduceIte, I64Values.set, hTyped] using hStateScale
    simpa only [result, scaled, hParams, parameters, value, Bool.false_eq_true, ↓reduceIte] using
      hNext result hReadyResult hStateResult
  | true =>
    simp only [↓reduceIte]
    apply biasCode_spec env initial weightsPtr inputPtr valuePtr scalePtr outputPtr weights input
      weightOffset scaleOffset biasOffset width outputWidth rows index _ afterScale
      hWeights (hBiasSize rfl) hCount hIndex hReadyScale hStateScale
    intro result hReadyResult hStateResult
    exact hNext result hReadyResult hStateResult

theorem outputWord_parts : outputWord =
    [.localGet 10, .constI64 1, .eqI64, .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
      .constI64 0, .eqI64, .eqz, .iff 0 1 (branch true) (branch false) [] [.i64]] := rfl

theorem outputWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat) (withBias : Bool) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hValues : ByteArrayAt initial.mem valuePtr.toNat (quantizeRows input 64 (rows * (width / 64))).values)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input 64 (rows * (width / 64))).scales)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hBiasSize : withBias = true → biasOffset + outputWidth * 4 ≤ weights.size)
    (hWidth : 0 < width) (hMultiple : 64 ∣ width) (hCount : rows * outputWidth < UInt64.size) (hIndex : index < rows * outputWidth)
    (hReady : PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr frame)
    (hState : OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result →
      OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
        width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (value weights input weightOffset scaleOffset biasOffset width outputWidth rows index withBias).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (outputWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  have hBranch (post : Assertion Unit)
      (hPost : ∀ result, PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result →
        OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
          width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows result →
        post (.Fallthrough initial { result with values :=
          [.i64 (value weights input weightOffset scaleOffset biasOffset width outputWidth rows index withBias).toUInt64,
            .i32 (PackedGenerateLoop.address outputPtr index)] })) :
      wp «module» (branch withBias) post initial
        { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
    have h := branch_spec env initial weightsPtr inputPtr valuePtr scalePtr outputPtr weights input
      weightOffset scaleOffset biasOffset width outputWidth rows index withBias frame
      hWeights hValues hScales hWeightSize hScaleSize hBiasSize hWidth hMultiple hCount hIndex hReady hState post []
      (by intro result hReady hState; simpa only [wp_nil] using hPost result hReady hState)
    simpa only [List.append_nil] using h
  have hParams := hState.1
  rw [outputWord_parts]
  simp only [List.cons_append, List.nil_append]
  cases withBias
  all_goals
    wp_packed_frame [hParams, parameters, List.getElem?_cons_zero, List.getElem?_cons_succ]
    refine wp_iff_cons rfl ?_
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    wp_packed_frame [hParams, parameters]
    refine wp_iff_cons rfl ?_
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    simp only [hParams, parameters, Bool.false_eq_true, ↓reduceIte] at hBranch
    apply hBranch
    intro result hReady hState
    exact hNext result hReady hState

#print axioms branch_spec
#print axioms outputWord_spec

end Project.Gpt2QuantizedGroupedRows.Projection
