import Project.Gpt2CachedStep.CachedRowSum.FrozenSpec
import Project.Gpt2CachedStep.CachedAttention.FrozenSource
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def sumsBody : Wasm.Program :=
  match (func29[215]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def sumsWord : Wasm.Program := (sumsBody.drop 12).take (sumsBody.length - 19)

set_option maxRecDepth 32768 in
theorem emitted_sums : (func29.drop 215).take 1 = PackedGenerateLoop.program 52 109 110 sumsWord := rfl

def SumsState (params saved : List Wasm.Value) (exponentialPtr : UInt64) (exponentialValues : ByteArray)
    (position : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.params.length = 8 ∧ frame.locals.length = 114 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (position + 1))) ∧
  frame.locals[40]? = some (.i64 exponentialPtr) ∧ frame.locals[41]? = some (.i64 exponentialPtr) ∧
  frame.locals[42]? = some (.i64 (UInt64.ofNat exponentialValues.size)) ∧
  frame.locals[43]? = some (.i64 48) ∧ I64Values frame.locals ∧ frame.locals.take 43 = saved

set_option maxRecDepth 32768 in
theorem sumsWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved : List Wasm.Value) (exponentialPtr outputPtr : UInt64) (exponentialValues : ByteArray)
    (position index : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem exponentialPtr.toNat exponentialValues)
    (hRow : (index + 1) * (position + 1) * 4 ≤ exponentialValues.size)
    (hReady : PackedGenerateLoop.Ready 52 109 110 12 index outputPtr frame)
    (hState : SumsState params saved exponentialPtr exponentialValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 52 109 110 12 index outputPtr result →
      SumsState params saved exponentialPtr exponentialValues position result →
      wp «module» rest Q initial { result with values :=
        [.i64 (cachedRowSum exponentialValues index (position + 1)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (sumsWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hParamLength, hLength, hSize, hOwner, hInputPtr, hInputBytes, hBytes, hTyped, hPrefix⟩
  have hParamsLength : params.length = 8 := by rw [← hParams]; exact hParamLength
  have hCounter : frame.locals[44]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[101]? = some (.i64 48) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.1
  have hPointer : frame.locals[102]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.2.1
  simp only [sumsWord, sumsBody, func29, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParamLength, hLength, hCounter, hSize, hOwner, hInputPtr, hInputBytes]
  refine wp_call_tw ((CachedRowSum.Spec.cachedRowSum_exact env initial exponentialPtr exponentialPtr
    exponentialValues index (position + 1) hInput hRow (Nat.succ_pos position)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 52 109 110 12 index outputPtr result ∧
      SumsState params saved exponentialPtr exponentialValues position result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (cachedRowSum exponentialValues index (position + 1)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hParamLength, hLength, List.length_set,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and,
        show UInt64.ofNat (4 * 12) = 48 from rfl]
    · simp (config := { maxDischargeDepth := 64 }) only [SumsState, hParams, hParamsLength, hLength, List.length_set, List.getElem?_set,
        Nat.reduceEqDiff, reduceIte, hSize, hOwner, hInputPtr, hInputBytes, hBytes, I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem sumsState_advance (params saved : List Wasm.Value) (exponentialPtr : UInt64) (exponentialValues : ByteArray)
    (position : Nat) (frame : Locals) (index : Nat) (hValid : frame.validIndex 52)
    (hState : SumsState params saved exponentialPtr exponentialValues position frame) :
    SumsState params saved exponentialPtr exponentialValues position (FixedArrayCopy.counterFrame frame 52 index hValid) := by
  rcases hState with ⟨hParams, hParamLength, hLength, hSize, hOwner, hInputPtr, hInputBytes, hBytes, hTyped, hPrefix⟩
  have hParamsLength : params.length = 8 := by rw [← hParams]; exact hParamLength
  simp (config := { maxDischargeDepth := 64 }) only [SumsState, FixedArrayCopy.counterFrame, Locals.set,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hParams, hParamsLength, hSize, hOwner, hInputPtr, hInputBytes, hBytes,
    I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]

set_option maxRecDepth 32768 in
theorem sumsLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (params saved : List Wasm.Value) (exponentialPtr outputPtr : UInt64) (exponentialValues : ByteArray)
    (position : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem exponentialPtr.toNat exponentialValues) (hInputSize : 12 * (position + 1) * 4 ≤ exponentialValues.size)
    (hFit : outputPtr.toNat + 48 ≤ 2^32)
    (hMemory : outputPtr.toNat + 48 ≤ initial.mem.pages * 65536)
    (hSep : exponentialPtr.toNat + exponentialValues.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 48 ≤ exponentialPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 52 109 110 12 0 outputPtr frame)
    (hState : SumsState params saved exponentialPtr exponentialValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 52 109 110 12 12 outputPtr result →
      SumsState params saved exponentialPtr exponentialValues position result →
      ByteArrayAt final.mem outputPtr.toNat (sums exponentialValues (position + 1)) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 48) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 215).take 1 ++ rest) Q initial frame env := by
  rw [emitted_sums]
  apply PackedGenerateLoop.program_spec (value := fun index => cachedRowSum exponentialValues index (position + 1))
    (P := SumsState params saved exponentialPtr exponentialValues position)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact sumsState_advance params saved exponentialPtr exponentialValues position next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    apply sumsWord_spec env current params saved exponentialPtr outputPtr exponentialValues position index next
      (hInput.writesRange hWrites hSep) _ hReady hState Q rest hNext
    exact (Nat.mul_le_mul_right 4 (Nat.mul_le_mul_right (position + 1)
      (show index + 1 ≤ 12 by omega))).trans hInputSize
  · exact hDone

#print axioms sumsWord_spec
#print axioms sumsLoop_spec

end Project.Gpt2CachedStep.Frozen.CachedAttention
