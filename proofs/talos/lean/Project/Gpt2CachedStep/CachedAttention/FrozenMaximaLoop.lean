import Project.Gpt2CachedStep.CachedRowMaximum.FrozenSpec
import Project.Gpt2CachedStep.CachedAttention.FrozenSource
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def maximaBody : Wasm.Program :=
  match (func29[110]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def maximaWord : Wasm.Program := (maximaBody.drop 12).take (maximaBody.length - 19)

set_option maxRecDepth 32768 in
theorem emitted_maxima : (func29.drop 110).take 1 = PackedGenerateLoop.program 26 109 110 maximaWord := rfl

def MaximaState (params : List Wasm.Value) (scorePtr : UInt64) (scoreValues : ByteArray)
    (position : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.params.length = 8 ∧ frame.locals.length = 114 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (position + 1))) ∧
  frame.locals[14]? = some (.i64 scorePtr) ∧ frame.locals[15]? = some (.i64 scorePtr) ∧
  frame.locals[16]? = some (.i64 (UInt64.ofNat scoreValues.size)) ∧
  frame.locals[17]? = some (.i64 48) ∧ I64Values frame.locals

set_option maxRecDepth 32768 in
theorem maximaWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (params : List Wasm.Value) (scorePtr outputPtr : UInt64) (scoreValues : ByteArray)
    (position index : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem scorePtr.toNat scoreValues)
    (hRow : (index + 1) * (position + 1) * 4 ≤ scoreValues.size)
    (hReady : PackedGenerateLoop.Ready 26 109 110 12 index outputPtr frame)
    (hState : MaximaState params scorePtr scoreValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 26 109 110 12 index outputPtr result →
      MaximaState params scorePtr scoreValues position result →
      wp «module» rest Q initial { result with values :=
        [.i64 (cachedRowMaximum scoreValues index (position + 1)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (maximaWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hParamLength, hLength, hSize, hOwner, hInputPtr, hInputBytes, hBytes, hTyped⟩
  have hParamsLength : params.length = 8 := by rw [← hParams]; exact hParamLength
  have hCounter : frame.locals[18]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[101]? = some (.i64 48) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.1
  have hPointer : frame.locals[102]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.2.1
  simp only [maximaWord, maximaBody, func29, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParamLength, hLength, hCounter, hSize, hOwner, hInputPtr, hInputBytes]
  refine wp_call_tw ((CachedRowMaximum.Spec.cachedRowMaximum_exact env initial scorePtr scorePtr
    scoreValues index (position + 1) hInput hRow (Nat.succ_pos position)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 26 109 110 12 index outputPtr result ∧
      MaximaState params scorePtr scoreValues position result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (cachedRowMaximum scoreValues index (position + 1)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hParamLength, hLength, List.length_set,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and,
        show UInt64.ofNat (4 * 12) = 48 from rfl]
    · simp (config := { maxDischargeDepth := 64 }) only [MaximaState, hParams, hParamsLength, hLength, List.length_set, List.getElem?_set,
        Nat.reduceEqDiff, reduceIte, hSize, hOwner, hInputPtr, hInputBytes, hBytes, I64Values.set, hTyped, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem maximaState_advance (params : List Wasm.Value) (scorePtr : UInt64) (scoreValues : ByteArray)
    (position : Nat) (frame : Locals) (index : Nat) (hValid : frame.validIndex 26)
    (hState : MaximaState params scorePtr scoreValues position frame) :
    MaximaState params scorePtr scoreValues position (FixedArrayCopy.counterFrame frame 26 index hValid) := by
  rcases hState with ⟨hParams, hParamLength, hLength, hSize, hOwner, hInputPtr, hInputBytes, hBytes, hTyped⟩
  have hParamsLength : params.length = 8 := by rw [← hParams]; exact hParamLength
  simp (config := { maxDischargeDepth := 64 }) only [MaximaState, FixedArrayCopy.counterFrame, Locals.set,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hParams, hParamsLength, hSize, hOwner, hInputPtr, hInputBytes, hBytes,
    I64Values.set, hTyped, and_self]

set_option maxRecDepth 32768 in
theorem maximaLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (params : List Wasm.Value) (scorePtr outputPtr : UInt64) (scoreValues : ByteArray)
    (position : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem scorePtr.toNat scoreValues) (hInputSize : 12 * (position + 1) * 4 ≤ scoreValues.size)
    (hFit : outputPtr.toNat + 48 ≤ 2^32)
    (hMemory : outputPtr.toNat + 48 ≤ initial.mem.pages * 65536)
    (hSep : scorePtr.toNat + scoreValues.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 48 ≤ scorePtr.toNat)
    (hReady : PackedGenerateLoop.Ready 26 109 110 12 0 outputPtr frame)
    (hState : MaximaState params scorePtr scoreValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 26 109 110 12 12 outputPtr result →
      MaximaState params scorePtr scoreValues position result →
      ByteArrayAt final.mem outputPtr.toNat (maxima scoreValues (position + 1)) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 48) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 110).take 1 ++ rest) Q initial frame env := by
  rw [emitted_maxima]
  apply PackedGenerateLoop.program_spec (value := fun index => cachedRowMaximum scoreValues index (position + 1))
    (P := MaximaState params scorePtr scoreValues position)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact maximaState_advance params scorePtr scoreValues position next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    apply maximaWord_spec env current params scorePtr outputPtr scoreValues position index next
      (hInput.writesRange hWrites hSep) _ hReady hState Q rest hNext
    exact (Nat.mul_le_mul_right 4 (Nat.mul_le_mul_right (position + 1)
      (show index + 1 ≤ 12 by omega))).trans hInputSize
  · exact hDone

#print axioms maximaWord_spec
#print axioms maximaLoop_spec

end Project.Gpt2CachedStep.Frozen.CachedAttention
