import Project.Gpt2CachedStep.ExpNeg.Spec
import Project.Gpt2CachedStep.CachedAttention.Source
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.PackedWordRead
import Project.ProofKit.F32Sub
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.CachedAttention
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def exponentialsBody : Wasm.Program :=
  match (func29[166]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def exponentialsWord : Wasm.Program := (exponentialsBody.drop 12).take (exponentialsBody.length - 19)

set_option maxRecDepth 32768 in
theorem emitted_exponentials : (func29.drop 166).take 1 =
    PackedGenerateLoop.program 37 109 110 exponentialsWord := rfl

def ExponentialsState (params : List Wasm.Value) (scorePtr maximumPtr : UInt64)
    (scoreValues maximumValues : ByteArray) (position : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.params.length = 8 ∧ frame.locals.length = 114 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (position + 1))) ∧
  frame.locals[14]? = some (.i64 scorePtr) ∧ frame.locals[15]? = some (.i64 scorePtr) ∧
  frame.locals[16]? = some (.i64 (UInt64.ofNat scoreValues.size)) ∧
  frame.locals[25]? = some (.i64 maximumPtr) ∧ frame.locals[26]? = some (.i64 maximumPtr) ∧
  frame.locals[27]? = some (.i64 (UInt64.ofNat maximumValues.size)) ∧
  frame.locals[28]? = some (.i64 (UInt64.ofNat (4 * (12 * (position + 1))))) ∧ I64Values frame.locals

set_option maxRecDepth 32768 in
theorem exponentialsWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (params : List Wasm.Value) (scorePtr maximumPtr outputPtr : UInt64)
    (scoreValues maximumValues : ByteArray) (position index : Nat) (frame : Locals)
    (hScores : ByteArrayAt initial.mem scorePtr.toNat scoreValues)
    (hMaxima : ByteArrayAt initial.mem maximumPtr.toNat maximumValues)
    (hScoreSize : 4 * (12 * (position + 1)) ≤ scoreValues.size) (hMaximumSize : 48 ≤ maximumValues.size)
    (hPosition : position < 128) (hIndex : index < 12 * (position + 1))
    (hReady : PackedGenerateLoop.Ready 37 109 110 (12 * (position + 1)) index outputPtr frame)
    (hState : ExponentialsState params scorePtr maximumPtr scoreValues maximumValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 37 109 110 (12 * (position + 1)) index outputPtr result →
      ExponentialsState params scorePtr maximumPtr scoreValues maximumValues position result →
      wp «module» rest Q initial { result with values :=
        [.i64 (expNeg (LeanExe.Float32.subBits (word scoreValues index)
          (word maximumValues (index / (position + 1))))).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (exponentialsWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hParamLength, hLength, hSize, hScoreOwner, hScorePtr, hScoreBytes,
    hMaximumOwner, hMaximumPtr, hMaximumBytes, hBytes, hTyped⟩
  have hParamsLength : params.length = 8 := by rw [← hParams]; exact hParamLength
  have hCounter : frame.locals[29]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[101]? = some (.i64 (UInt64.ofNat (4 * (12 * (position + 1))))) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.1
  have hPointer : frame.locals[102]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParamLength, hLength] using hReady.2.2.2.1
  have hSize64 : position + 1 < 2^64 := by omega
  have hIndex64 : index < 2^64 := by omega
  have hNonzero : UInt64.ofNat (position + 1) ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hSize64] at this
    change position + 1 = 0 at this
    omega
  have hDiv : UInt64.ofNat index / UInt64.ofNat (position + 1) = UInt64.ofNat (index / (position + 1)) := by
    symm
    exact UInt64.ofNat_div hIndex64 hSize64
  have hHead : index / (position + 1) < 12 :=
    (Nat.div_lt_iff_lt_mul (Nat.succ_pos position)).mpr hIndex
  simp only [exponentialsWord, exponentialsBody, func29, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParamLength, hLength, hCounter, hScoreOwner, hScorePtr, hScoreBytes]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial
    scorePtr scorePtr scoreValues index hScores (by omega)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParamLength, hLength, hCounter, hSize, hMaximumOwner, hMaximumPtr, hMaximumBytes, hNonzero, hDiv]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParamLength, hLength, hCounter, hSize, hNonzero, hDiv]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env final
    maximumPtr maximumPtr maximumValues (index / (position + 1)) hMaxima (by omega)).append_args
    rfl rfl rfl [.f32 (word scoreValues index), .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParamLength, hLength]
  refine wp_call_tw ((ExpNeg.Spec.expNeg_exact env final
    (Wasm.IEEE32.sub (word scoreValues index) (word maximumValues (index / (position + 1))))).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  simp only [F32Sub.sub_eq] at hNext
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 37 109 110 (12 * (position + 1)) index outputPtr result ∧
      ExponentialsState params scorePtr maximumPtr scoreValues maximumValues position result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (expNeg (Wasm.IEEE32.sub (word scoreValues index)
      (word maximumValues (index / (position + 1))))).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hParamLength, hLength, List.length_set, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        reduceIte, List.getElem?_set, Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
    · simp (config := { maxDischargeDepth := 64 }) only [ExponentialsState, hParams, hParamsLength, hLength,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte, hSize,
        hScoreOwner, hScorePtr, hScoreBytes, hMaximumOwner, hMaximumPtr, hMaximumBytes,
        hBytes, I64Values.set, hTyped, and_self]
  · intro result h
    exact hNext result h.1 h.2

theorem exponentialsState_advance (params : List Wasm.Value) (scorePtr maximumPtr : UInt64)
    (scoreValues maximumValues : ByteArray) (position : Nat) (frame : Locals) (index : Nat)
    (hValid : frame.validIndex 37)
    (hState : ExponentialsState params scorePtr maximumPtr scoreValues maximumValues position frame) :
    ExponentialsState params scorePtr maximumPtr scoreValues maximumValues position
      (FixedArrayCopy.counterFrame frame 37 index hValid) := by
  rcases hState with ⟨hParams, hParamLength, hLength, hSize, hScoreOwner, hScorePtr, hScoreBytes,
    hMaximumOwner, hMaximumPtr, hMaximumBytes, hBytes, hTyped⟩
  have hParamsLength : params.length = 8 := by rw [← hParams]; exact hParamLength
  simp (config := { maxDischargeDepth := 64 }) only [ExponentialsState, FixedArrayCopy.counterFrame, Locals.set,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hParams, hParamsLength, hSize,
    hScoreOwner, hScorePtr, hScoreBytes, hMaximumOwner, hMaximumPtr, hMaximumBytes,
    hBytes, I64Values.set, hTyped, and_self]

set_option maxRecDepth 32768 in
theorem exponentialsLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (params : List Wasm.Value) (scorePtr maximumPtr outputPtr : UInt64)
    (scoreValues maximumValues : ByteArray) (position : Nat) (frame : Locals)
    (hScores : ByteArrayAt initial.mem scorePtr.toNat scoreValues)
    (hMaxima : ByteArrayAt initial.mem maximumPtr.toNat maximumValues)
    (hScoreSize : 4 * (12 * (position + 1)) ≤ scoreValues.size) (hMaximumSize : 48 ≤ maximumValues.size)
    (hPosition : position < 128)
    (hFit : outputPtr.toNat + 4 * (12 * (position + 1)) ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * (12 * (position + 1)) ≤ initial.mem.pages * 65536)
    (hScoreSep : scorePtr.toNat + scoreValues.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (12 * (position + 1)) ≤ scorePtr.toNat)
    (hMaximumSep : maximumPtr.toNat + maximumValues.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (12 * (position + 1)) ≤ maximumPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 37 109 110 (12 * (position + 1)) 0 outputPtr frame)
    (hState : ExponentialsState params scorePtr maximumPtr scoreValues maximumValues position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 37 109 110 (12 * (position + 1)) (12 * (position + 1)) outputPtr result →
      ExponentialsState params scorePtr maximumPtr scoreValues maximumValues position result →
      ByteArrayAt final.mem outputPtr.toNat (exponentials scoreValues maximumValues (position + 1)) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * (12 * (position + 1))) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 166).take 1 ++ rest) Q initial frame env := by
  rw [emitted_exponentials]
  apply PackedGenerateLoop.program_spec
    (value := fun index => expNeg (LeanExe.Float32.subBits (word scoreValues index)
      (word maximumValues (index / (position + 1)))))
    (P := ExponentialsState params scorePtr maximumPtr scoreValues maximumValues position)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact exponentialsState_advance params scorePtr maximumPtr scoreValues maximumValues position next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact exponentialsWord_spec env current params scorePtr maximumPtr outputPtr scoreValues maximumValues position index next
      (hScores.writesRange hWrites hScoreSep) (hMaxima.writesRange hWrites hMaximumSep)
      hScoreSize hMaximumSize hPosition hIndex hReady hState Q rest hNext
  · exact hDone

#print axioms exponentialsWord_spec
#print axioms exponentialsLoop_spec

end Project.Gpt2CachedStep.CachedAttention
