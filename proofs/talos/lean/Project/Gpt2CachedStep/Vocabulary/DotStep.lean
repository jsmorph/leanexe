import Project.Gpt2CachedStep.Program
import Project.Gpt2CachedStep.Vocabulary.Source
import Project.ProofKit.Annotation
import Project.ProofKit.PackedWordRead
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.CheckedNatMulArithmetic
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.Vocabulary
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def outerBody : Wasm.Program := (Annotation.resolve func37 [⟨42, .block⟩, ⟨0, .loop⟩]).getD []

def dotStep : Wasm.Program :=
  ((Annotation.resolve outerBody [⟨24, .block⟩, ⟨0, .loop⟩]).getD []).drop 4 |>.dropLast

def parameters (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray) : List Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
   .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size)]

def Saved (original frame : Locals) : Prop :=
  frame.locals[0]? = original.locals[0]? ∧ frame.locals[1]? = original.locals[1]? ∧
  frame.locals[22]? = original.locals[22]? ∧ frame.locals[23]? = original.locals[23]?

def Accumulator (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (token index : Nat) (original frame : Locals) : Prop :=
  frame.params = parameters weightsOwner inputOwner weightsPtr inputPtr weights input ∧
  frame.locals.length = 35 ∧ frame.locals[1]? = some (.i64 (UInt64.ofNat token)) ∧
  frame.locals[3]? = some (.i64 (dotPrefix weights input token index).toUInt64) ∧
  frame.locals[26]? = some (.i64 1) ∧ Saved original frame ∧ I64Values frame.locals

def dotStepCode : Wasm.Program :=
  [.localGet 30, .localSet 10, .localGet 9, .localSet 11, .localGet 11, .wrapI64, .f32ReinterpretI32,
   .localGet 3, .localSet 12, .localGet 4, .localSet 13, .localGet 5, .localSet 14,
   .localGet 10, .localSet 15, .localGet 12, .localGet 13, .localGet 14, .localGet 15, .call 17,
   .wrapI64, .f32ReinterpretI32,
   .localGet 0, .localSet 16, .localGet 1, .localSet 17, .localGet 2, .localSet 18,
   .localGet 7, .localSet 36, .constI64 768, .localSet 37,
   .localGet 37, .constI64 0, .eqI64,
   .iff 0 1 [.constI64 0]
     [.constI64 (-1), .localGet 37, .divUI64, .localGet 36, .ltUI64,
      .iff 0 1 [.unreachable] [.localGet 36, .localGet 37, .mulI64] [] [.i64]] [] [.i64],
   .localSet 33, .localGet 10, .localSet 34,
   .localGet 33, .localGet 34, .addI64, .localTee 35, .localGet 33, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 35] [] [.i64], .localSet 19,
   .localGet 16, .localGet 17, .localGet 18, .localGet 19, .call 17,
   .wrapI64, .f32ReinterpretI32, .f32Mul, .i32ReinterpretF32, .extendUI32,
   .wrapI64, .f32ReinterpretI32, .f32Add, .i32ReinterpretF32, .extendUI32,
   .localSet 20, .localGet 20, .localSet 21, .localGet 21, .localSet 39,
   .constI64 0, .localSet 38, .localGet 39, .localSet 9, .constI64 1, .localSet 40,
   .localGet 38, .constI64 0, .neI64, .br_if 1,
   .localGet 30, .localSet 33, .localGet 32, .localSet 34,
   .localGet 33, .localGet 34, .addI64, .localTee 35, .localGet 33, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 35] [] [.i64], .localSet 30]

set_option maxRecDepth 32768 in
theorem emitted_dotStep : dotStep = dotStepCode := rfl

theorem dotStep_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (token index : Nat) (original frame : Locals) (values : List Value)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputSize : 3072 ≤ input.size) (hWeightsSize : 50257 * 768 * 4 ≤ weights.size)
    (hToken : token < 50257) (hIndex : index < 768)
    (hReady : RangeFoldLoop.Ready 30 31 768 index frame values)
    (hAcc : Accumulator weightsOwner inputOwner weightsPtr inputPtr weights input token index original frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, RangeFoldLoop.Ready 30 31 768 (index + 1) result values →
      Accumulator weightsOwner inputOwner weightsPtr inputPtr weights input token (index + 1) original result →
      wp «module» rest Q initial result env) :
    wp «module» (dotStep ++ rest) Q initial frame env := by
  rcases hAcc with ⟨hParams, hLength, hTokenLocal, hTotal, hStride, hSaved, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[24]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hStop : frame.locals[25]? = some (.i64 768) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2
  have hMul : ¬(-1 : UInt64) / 768 < UInt64.ofNat token := by
    change ¬(24019198012642645 : UInt64) < UInt64.ofNat token
    u64_omega
  have hAdd : ¬ UInt64.ofNat token * 768 + UInt64.ofNat index < UInt64.ofNat token * 768 := by
    simpa only [UInt64.ofNat_mul, show UInt64.ofNat 768 = 768 from rfl] using
      CheckedNatAdd.guard_of_fits (token * 768) index
        (by change token * 768 + index < 18446744073709551616; omega)
  have hInc : ¬ UInt64.ofNat index + 1 < UInt64.ofNat index := by u64_omega
  have hIndexAdd : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
  have hAddress : UInt64.ofNat token * 768 + UInt64.ofNat index = UInt64.ofNat (token * 768 + index) := by simp
  rw [emitted_dotStep]
  simp only [dotStepCode, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hTotal, hCounter, hReady.1]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial inputOwner inputPtr input
    index hInput (by omega)).append_args rfl rfl rfl (.f32 (dotPrefix weights input token index) :: values)) ?_
  rintro final returned ⟨_, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, hLength, hTokenLocal, hCounter]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hMul, hAdd])])
  simp only [hAddress]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env final weightsOwner weightsPtr weights
    (token * 768 + index) hWeights (by omega)).append_args rfl rfl rfl
      (.f32 (word input index) :: .f32 (dotPrefix weights input token index) :: values)) ?_
  rintro final' returned ⟨_, rfl, rfl, rfl⟩
  wp_packed_frame [hParams, hLength, hCounter, hStride]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hInc)]
  wp_packed_frame [hParams, hLength]
  apply hNext
  · simp only [RangeFoldLoop.Ready, Locals.get, hLength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hStop, hIndexAdd, true_and]
    rfl
  · simpa (config := { maxDischargeDepth := 64 }) only [Accumulator, parameters, Saved, hLength,
      List.length_set, List.getElem?_set, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hTokenLocal, hStride,
      dotPrefix_succ, word, I64Values.set, hTyped, true_and, and_true, and_self] using hSaved

#print axioms dotStep_spec

end Project.Gpt2CachedStep.Vocabulary
