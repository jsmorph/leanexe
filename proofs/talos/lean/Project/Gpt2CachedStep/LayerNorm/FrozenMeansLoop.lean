import Project.Gpt2CachedStep.FrozenRowMean
import Project.Gpt2CachedStep.LayerNorm.FrozenSource
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.Frozen.LayerNorm
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def parameters (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (scaleOffset biasOffset rows : Nat) : List Wasm.Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
    .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size),
    .i64 (UInt64.ofNat scaleOffset), .i64 (UInt64.ofNat biasOffset), .i64 (UInt64.ofNat rows)]

def meansBody : Wasm.Program :=
  match (func20[42]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def meansWord : Wasm.Program := (meansBody.drop 12).take 13

set_option maxRecDepth 32768 in
theorem emitted_means : (func20.drop 42).take 1 = PackedGenerateLoop.program 10 70 71 meansWord := rfl

def MeansState (params : List Wasm.Value) (rows : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 74 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧ I64Values frame.locals

set_option maxRecDepth 32768 in
theorem meansWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr outputPtr : UInt64) (weights input : ByteArray)
    (scaleOffset biasOffset rows index : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hRow : (index + 1) * 768 * 4 ≤ input.size)
    (hReady : PackedGenerateLoop.Ready 10 70 71 rows index outputPtr frame)
    (hState : MeansState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 10 70 71 rows index outputPtr result →
      MeansState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
        scaleOffset biasOffset rows) rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (rowMean input index).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (meansWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[1]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[61]? = some (.i64 (UInt64.ofNat (4 * rows))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[62]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  simp only [meansWord, meansBody, func20, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_call_tw ((RowMean.rowMean_exact env initial inputOwner inputPtr input index hInput hRow).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 10 70 71 rows index outputPtr result ∧
      MeansState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
        scaleOffset biasOffset rows) rows result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (rowMean input index).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
    · simp (config := { maxDischargeDepth := 64 }) only [MeansState, parameters, hLength, List.length_set, List.getElem?_set,
        Nat.reduceEqDiff, reduceIte, hBytes, I64Values.set, hTyped, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem meansState_advance (params : List Wasm.Value) (rows : Nat) (hParams : params.length = 9)
    (frame : Locals) (index : Nat) (hValid : frame.validIndex 10)
    (hState : MeansState params rows frame) :
    MeansState params rows (FixedArrayCopy.counterFrame frame 10 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [MeansState, FixedArrayCopy.counterFrame, Locals.set, hFrameParams, hParams,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hBytes, I64Values.set, hTyped, and_self]

set_option maxRecDepth 32768 in
theorem meansLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr outputPtr : UInt64) (weights input : ByteArray)
    (scaleOffset biasOffset rows : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input) (hInputSize : rows * 768 * 4 ≤ input.size)
    (hFit : outputPtr.toNat + 4 * rows ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * rows ≤ initial.mem.pages * 65536)
    (hSep : inputPtr.toNat + input.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 4 * rows ≤ inputPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 10 70 71 rows 0 outputPtr frame)
    (hState : MeansState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 10 70 71 rows rows outputPtr result →
      MeansState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
        scaleOffset biasOffset rows) rows result →
      ByteArrayAt final.mem outputPtr.toNat (means input rows) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * rows) →
      wp «module» rest Q final result env) :
    wp «module» ((func20.drop 42).take 1 ++ rest) Q initial frame env := by
  rw [emitted_means]
  apply PackedGenerateLoop.program_spec (value := rowMean input)
    (P := MeansState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) rows)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact meansState_advance _ rows rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact meansWord_spec env current weightsOwner inputOwner weightsPtr inputPtr outputPtr
      weights input scaleOffset biasOffset rows index next (hInput.writesRange hWrites hSep)
      (by omega) hReady hState Q rest hNext
  · exact hDone

#print axioms meansWord_spec
#print axioms meansLoop_spec

end Project.Gpt2CachedStep.Frozen.LayerNorm
