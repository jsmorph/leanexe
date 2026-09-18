import Project.Gpt2CachedStep.LayerNorm.VarianceStep

namespace Project.Gpt2CachedStep.LayerNorm
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2
open Project.Gpt2RowInvStd (variancePrefix variancePrefix_zero rowInvStd_eq)

def inversesWord : Wasm.Program := (inversesBody.drop 12).take 57

set_option maxRecDepth 32768 in
theorem emitted_variance : inversesWord = inversesWord.take 14 ++
    RangeFoldLoop.program 72 73 varianceStep ++ inversesWord.drop 15 := rfl

set_option maxRecDepth 32768 in
theorem emitted_inverses : (func20.drop 91).take 1 =
    PackedGenerateLoop.program 20 70 71 inversesWord := rfl

set_option maxRecDepth 32768 in
theorem inversesWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr meansOwner meansPtr outputPtr : UInt64)
    (weights input : ByteArray) (scaleOffset biasOffset rows row : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hMeans : ByteArrayAt initial.mem meansPtr.toNat (means input rows))
    (hRow : (row + 1) * 768 * 4 ≤ input.size) (hRows : row < rows)
    (hReady : PackedGenerateLoop.Ready 20 70 71 rows row outputPtr frame)
    (hState : InversesState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) meansOwner meansPtr rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 20 70 71 rows row outputPtr result →
      InversesState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
        scaleOffset biasOffset rows) meansOwner meansPtr rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (rowInvStd input row (word (means input rows) row)).toUInt64,
         .i32 (PackedGenerateLoop.address outputPtr row)] } env) :
    wp «module» (inversesWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr row)] } env := by
  rcases hState with ⟨hParams, hLength, hMeansOwner, hMeansPtr, hMeansSize, hBytes⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[11]? = some (.i64 (UInt64.ofNat row)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[61]? = some (.i64 (UInt64.ofNat (4 * rows))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[62]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  rw [emitted_variance]
  simp only [List.append_assoc, inversesWord, inversesBody, func20,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, List.drop,
    List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength]
  apply RangeFoldLoop.program_spec_with_stack
    (values := [.i32 (PackedGenerateLoop.address outputPtr row)]) (count := 768)
    (P := fun index => VarianceState
      (parameters weightsOwner inputOwner weightsPtr inputPtr weights input scaleOffset biasOffset rows)
      input meansOwner meansPtr outputPtr rows row index)
  · decide
  · simp [RangeFoldLoop.Ready, Locals.get, hLength]
  · simp only [VarianceState, InversesState, parameters, hLength, List.length_set,
      List.getElem?_set, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hMeansOwner, hMeansPtr,
      hMeansSize, hBytes, hCounter, hLengthLocal, hPointer, variancePrefix_zero, and_self]
    decide
  · intro index next hIndex hReady hState Q rest hNext
    exact varianceStep_spec env initial weightsOwner inputOwner weightsPtr inputPtr meansOwner meansPtr
      outputPtr weights input scaleOffset biasOffset rows row index next
      [.i32 (PackedGenerateLoop.address outputPtr row)] hInput hMeans hRow hRows hIndex
      hReady hState Q rest hNext
  · intro result hReady hState
    rcases hState with ⟨⟨hResultParams, hResultLength, hMeanOwner, hMeanPtr, hMeanSize, hByteLength⟩,
      hRowLocal, hTotal, hSize, hPtr, _⟩
    simp only [parameters] at hResultParams
    wp_packed_frame [hResultParams, hResultLength, hTotal, hReady.1]
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 20 70 71 rows row outputPtr result ∧
        InversesState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
          scaleOffset biasOffset rows) meansOwner meansPtr rows result)
      (R := fun result => wp «module» rest Q initial result env)
      (values := [.i64 (rowInvStd input row (word (means input rows) row)).toUInt64,
        .i32 (PackedGenerateLoop.address outputPtr row)]) (by rw [rowInvStd_eq]; rfl)
    · constructor
      · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
          hResultLength, List.length_set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
          Nat.reduceEqDiff, hRowLocal, hSize, hPtr, true_and]
      · simp only [InversesState, parameters, hResultLength, List.length_set, List.getElem?_set,
          Nat.reduceEqDiff, reduceIte, hMeanOwner, hMeanPtr, hMeanSize, hByteLength, and_self]
    · intro next h
      exact hNext next h.1 h.2

theorem inversesState_advance (params : List Wasm.Value) (meansOwner meansPtr : UInt64)
    (rows : Nat) (hParams : params.length = 9) (frame : Locals) (index : Nat)
    (hValid : frame.validIndex 20) (hState : InversesState params meansOwner meansPtr rows frame) :
    InversesState params meansOwner meansPtr rows (FixedArrayCopy.counterFrame frame 20 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hOwner, hPtr, hSize, hBytes⟩
  simp only [InversesState, FixedArrayCopy.counterFrame, Locals.set, hFrameParams, hParams,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hOwner, hPtr, hSize, hBytes, and_self]

set_option maxRecDepth 32768 in
theorem inversesLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr meansOwner meansPtr outputPtr : UInt64)
    (weights input : ByteArray) (scaleOffset biasOffset rows : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input) (hInputSize : rows * 768 * 4 ≤ input.size)
    (hMeans : ByteArrayAt initial.mem meansPtr.toNat (means input rows))
    (hFit : outputPtr.toNat + 4 * rows ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * rows ≤ initial.mem.pages * 65536)
    (hInputSep : inputPtr.toNat + input.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 4 * rows ≤ inputPtr.toNat)
    (hMeansSep : meansPtr.toNat + (means input rows).size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * rows ≤ meansPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 20 70 71 rows 0 outputPtr frame)
    (hState : InversesState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) meansOwner meansPtr rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 20 70 71 rows rows outputPtr result →
      InversesState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
        scaleOffset biasOffset rows) meansOwner meansPtr rows result →
      ByteArrayAt final.mem outputPtr.toNat (inverses input rows) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * rows) →
      wp «module» rest Q final result env) :
    wp «module» ((func20.drop 91).take 1 ++ rest) Q initial frame env := by
  rw [emitted_inverses]
  apply PackedGenerateLoop.program_spec (value := fun row => rowInvStd input row (word (means input rows) row))
    (P := InversesState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) meansOwner meansPtr rows)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact inversesState_advance _ meansOwner meansPtr rows rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact inversesWord_spec env current weightsOwner inputOwner weightsPtr inputPtr meansOwner meansPtr
      outputPtr weights input scaleOffset biasOffset rows index next
      (hInput.writesRange hWrites hInputSep) (hMeans.writesRange hWrites hMeansSep)
      (by omega) hIndex hReady hState Q rest hNext
  · exact hDone

#print axioms inversesWord_spec
#print axioms inversesLoop_spec

end Project.Gpt2CachedStep.LayerNorm
