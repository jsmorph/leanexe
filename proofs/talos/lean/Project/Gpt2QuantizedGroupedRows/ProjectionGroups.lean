import Project.Gpt2QuantizedGroupedRows.ProjectionGroup

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedGroupedRows.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem groupsLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat)
    (withBias : Bool) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hValues : ByteArrayAt initial.mem valuePtr.toNat (quantizeRows input 64 (rows * (width / 64))).values)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input 64 (rows * (width / 64))).scales)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hWidth : 0 < width) (hMultiple : 64 ∣ width) (hCount : rows * outputWidth < UInt64.size)
    (hIndex : index < rows * outputWidth)
    (hReady : PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr frame)
    (hGroupReady : RangeFoldLoop.Ready 95 96 (width / 64) 0 frame)
    (hAcc : Accumulator weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
      biasOffset width outputWidth rows index 0 withBias frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result →
      Accumulator weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
        biasOffset width outputWidth rows index (width / 64) withBias result →
      wp «module» rest Q initial { result with values :=
        [.i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (RangeFoldLoop.program 95 96 (groupStep withBias) ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  let P := fun group (next : Locals) =>
    PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr { next with values := [] } ∧
    Accumulator weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
      biasOffset width outputWidth rows index group withBias next
  have hGroups64 : width / 64 < UInt64.size := by
    have hRows : 0 < rows := by nlinarith
    have := hScales.1
    rw [grouped_scales_size] at this
    change _ < 18446744073709551616
    nlinarith
  apply RangeFoldLoop.program_spec_with_stack 95 96 (groupStep withBias) «module» env initial _
    [.i32 (PackedGenerateLoop.address outputPtr index)] (width / 64) P hGroups64
  · exact ⟨rfl, hGroupReady.2⟩
  · exact ⟨⟨rfl, hReady.2⟩, hAcc⟩
  · intro group next hGroup hGroupReady hP post tail hTail
    have hStep := group_spec env initial weightsPtr inputPtr valuePtr scalePtr outputPtr weights input
      weightOffset scaleOffset biasOffset width outputWidth rows index group withBias
      { next with values := [] } hWeights hValues hScales hWeightSize hScaleSize hWidth hMultiple
      hCount hIndex hGroup hP.1 ⟨rfl, hGroupReady.2⟩ hP.2 post tail
      (by
        intro result hReadyResult hGroupResult hAccResult
        exact hTail { result with values := [.i32 (PackedGenerateLoop.address outputPtr index)] }
          ⟨rfl, hGroupResult.2⟩ ⟨⟨rfl, hReadyResult.2⟩, hAccResult⟩)
    simpa only [← hGroupReady.1] using hStep
  · intro result hGroupResult hP
    have h := hNext { result with values := [] } hP.1 hP.2
    simpa only [← hGroupResult.1] using h

def groupsCode (withBias : Bool) : Wasm.Program :=
  (branch withBias).take 12 ++ RangeFoldLoop.program 95 96 (groupStep withBias)

set_option maxHeartbeats 1600000 in
theorem groupsCode_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index : Nat)
    (withBias : Bool) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hValues : ByteArrayAt initial.mem valuePtr.toNat (quantizeRows input 64 (rows * (width / 64))).values)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input 64 (rows * (width / 64))).scales)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hWidth : 0 < width) (hMultiple : 64 ∣ width) (hCount : rows * outputWidth < UInt64.size)
    (hIndex : index < rows * outputWidth)
    (hReady : PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr frame)
    (hState : OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result →
      Accumulator weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
        biasOffset width outputWidth rows index (width / 64) withBias result →
      wp «module» rest Q initial { result with values :=
        [.i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (groupsCode withBias ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  have hParams := hState.1
  have hLength := hState.2.1
  have hGroups := hState.2.2.1
  rcases hState with ⟨_, _, _, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr,
    hValueSize, hScaleCopyOwner, hScalePtr, hScaleLength, hBytes, hTyped⟩
  have hCounter : frame.locals[19]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, parameters, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[82]? = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth)))) := by
    simpa [Locals.get, hParams, parameters, hLength] using hReady.2.2.1
  have hPointer : frame.locals[83]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, parameters, hLength] using hReady.2.2.2.1
  cases withBias <;>
    simp only [groupsCode, branch, outputWord, outputBody, func8,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
  all_goals
    wp_packed_frame [hParams, parameters, hLength, hGroups]
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) index outputPtr result ∧
        RangeFoldLoop.Ready 95 96 (width / 64) 0 result ∧
        Accumulator weightsPtr inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
          biasOffset width outputWidth rows index 0 _ result)
      (R := fun result => wp «module» (RangeFoldLoop.program 95 96 (groupStep _) ++ rest) Q initial result env) rfl
    case hNext =>
      intro result h
      exact groupsLoop_spec env initial weightsPtr inputPtr valuePtr scalePtr outputPtr weights input
        weightOffset scaleOffset biasOffset width outputWidth rows index _ result hWeights hValues hScales
        hWeightSize hScaleSize hWidth hMultiple hCount hIndex h.1 h.2.1 h.2.2 Q rest hNext
    · constructor
      · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex, hParams, parameters,
          hLength, List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
          Nat.reduceSub, reduceIte, List.getElem?_set, Nat.reduceEqDiff,
          hCounter, hLengthLocal, hPointer, true_and]
      · constructor
        · simp only [RangeFoldLoop.Ready, Locals.get, hParams, parameters, hLength, List.length_set,
            List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
            reduceIte, List.getElem?_set, Nat.reduceEqDiff, true_and]
          exact ⟨rfl, trivial⟩
        · simp (config := { maxDischargeDepth := 64 }) only [Accumulator, OutputState, parameters,
            hParams, hLength, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT,
            Bool.false_eq_true, reduceIte, hGroups, hValueOwner, hScaleOwner, hValueCopyOwner,
            hValuePtr, hValueSize, hScaleCopyOwner, hScalePtr, hScaleLength, hBytes,
            I64Values.set, hTyped, sumPrefix_zero, and_self, true_and]
          exact ⟨rfl, trivial⟩

#print axioms groupsLoop_spec
#print axioms groupsCode_spec

end Project.Gpt2QuantizedGroupedRows.Projection
