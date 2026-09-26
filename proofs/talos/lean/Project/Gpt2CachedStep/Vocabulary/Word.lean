import Project.Gpt2CachedStep.Vocabulary.DotStep
import Project.ProofKit.PackedGenerateLoop

namespace Project.Gpt2CachedStep.Vocabulary
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame

def wordCode : Wasm.Program := (outerBody.drop 12).take 16

set_option maxRecDepth 32768 in
theorem emitted_word : wordCode =
    [.constI64 0, .localSet 8, .constI64 0, .localSet 30, .constI64 768, .localSet 31,
     .constI64 1, .localSet 32, .localGet 8, .localSet 9] ++
    RangeFoldLoop.program 30 31 dotStep ++ [.localGet 9, .localSet 22, .localGet 22, .localSet 23, .localGet 23] := rfl

set_option maxRecDepth 32768 in
theorem emitted_loop : (func37.drop 42).take 1 = PackedGenerateLoop.program 7 28 29 wordCode := rfl

def OutputState (params : List Value) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 35 ∧
  frame.locals[0]? = some (.i64 201028) ∧ I64Values frame.locals

theorem word_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr outputPtr : UInt64) (weights input : ByteArray)
    (token : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputSize : 3072 ≤ input.size) (hWeightsSize : 50257 * 768 * 4 ≤ weights.size)
    (hToken : token < 50257)
    (hReady : PackedGenerateLoop.Ready 7 28 29 50257 token outputPtr frame)
    (hState : OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input) frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 7 28 29 50257 token outputPtr result →
      OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input) result →
      wp «module» rest Q initial { result with values :=
        [.i64 (dotPrefix weights input token 768).toUInt64, .i32 (PackedGenerateLoop.address outputPtr token)] } env) :
    wp «module» (wordCode ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr token)] } env := by
  rcases hState with ⟨hParams, hLength, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[1]? = some (.i64 (UInt64.ofNat token)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[22]? = some (.i64 (UInt64.ofNat (4 * 50257))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointerLocal : frame.locals[23]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  rw [emitted_word]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength]
  apply RangeFoldLoop.program_spec_with_stack (values := [.i32 (PackedGenerateLoop.address outputPtr token)])
    (count := 768) (P := fun index => Accumulator weightsOwner inputOwner weightsPtr inputPtr weights input token index frame)
  · decide
  · simp [RangeFoldLoop.Ready, Locals.get, hLength]
  · simp (config := { maxDischargeDepth := 64 }) only [Accumulator, parameters, Saved, hLength,
      List.length_set, List.getElem?_set, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hCounter,
      dotPrefix_zero, show (0 : UInt32).toUInt64 = 0 from rfl, I64Values.set, hTyped, and_self]
  · intro index next hIndex hInnerReady hAcc Q rest hNext
    exact dotStep_spec env initial weightsOwner inputOwner weightsPtr inputPtr weights input token index frame next
      [.i32 (PackedGenerateLoop.address outputPtr token)] hWeights hInput hInputSize hWeightsSize hToken hIndex hInnerReady hAcc Q rest hNext
  · intro result hInnerReady hAcc
    rcases hAcc with ⟨hResultParams, hResultLength, _, hTotal, _, hSaved, hResultTyped⟩
    simp only [parameters] at hResultParams
    wp_packed_frame [hResultParams, hResultLength, hTotal, hInnerReady.1]
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 7 28 29 50257 token outputPtr result ∧
        OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input) result)
      (R := fun result => wp «module» rest Q initial result env)
      (values := [.i64 (dotPrefix weights input token 768).toUInt64, .i32 (PackedGenerateLoop.address outputPtr token)]) rfl
    · constructor
      · rcases hSaved with ⟨_, hs1, hs22, hs23⟩
        simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
          hResultLength, List.length_set, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
          Nat.reduceSub, reduceIte, List.getElem?_set, Nat.reduceEqDiff,
          hs1, hs22, hs23, hCounter, hLengthLocal, hPointerLocal, true_and]
      · simp only [OutputState, parameters, hResultLength, List.length_set, List.getElem?_set,
          Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hSaved.1, hBytes, I64Values.set, hResultTyped, and_self]
    · intro result h
      exact hNext result h.1 h.2

#print axioms word_spec

end Project.Gpt2CachedStep.Vocabulary
