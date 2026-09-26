import Project.Gpt2CachedStep.Vocabulary.FrozenWord

namespace Project.Gpt2CachedStep.Frozen.Vocabulary
open Wasm Project.Common Project.ProofKit PackedMemory LeanExe.Models.Gpt2

theorem outputState_advance (params : List Value) (hParams : params.length = 6)
    (frame : Locals) (index : Nat) (hValid : frame.validIndex 7) (hState : OutputState params frame) :
    OutputState params (FixedArrayCopy.counterFrame frame 7 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [OutputState, FixedArrayCopy.counterFrame, Locals.set,
    hFrameParams, hParams, hLength, List.length_set, List.getElem?_set, Nat.reduceSub,
    Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hBytes, I64Values.set, hTyped, and_self]

theorem loop_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr outputPtr : UInt64) (weights input : ByteArray) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputSize : 3072 ≤ input.size) (hWeightsSize : 50257 * 768 * 4 ≤ weights.size)
    (hFit : outputPtr.toNat + 201028 ≤ 2^32)
    (hMemory : outputPtr.toNat + 201028 ≤ initial.mem.pages * 65536)
    (hWeightsSep : weightsPtr.toNat + weights.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 201028 ≤ weightsPtr.toNat)
    (hInputSep : inputPtr.toNat + input.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 201028 ≤ inputPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 7 28 29 50257 0 outputPtr frame)
    (hState : OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input) frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 7 28 29 50257 50257 outputPtr result →
      OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input) result →
      ByteArrayAt final.mem outputPtr.toNat (vocabularyHead weights input) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 201028) →
      wp «module» rest Q final result env) :
    wp «module» ((func37.drop 42).take 1 ++ rest) Q initial frame env := by
  rw [emitted_loop]
  apply PackedGenerateLoop.program_spec (value := fun token => dotPrefix weights input token 768)
    (P := OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input))
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact outputState_advance _ rfl next index hValid hState
  · intro current next token hToken hReady hState hWrites Q rest hNext
    exact word_spec env current weightsOwner inputOwner weightsPtr inputPtr outputPtr weights input token next
      (hWeights.writesRange hWrites hWeightsSep) (hInput.writesRange hWrites hInputSep)
      hInputSize hWeightsSize hToken hReady hState Q rest hNext
  · intro final result hReady hState hBytes hWrites
    exact hDone final result hReady hState (by rwa [vocabularyHead_eq]) hWrites

#print axioms loop_spec

end Project.Gpt2CachedStep.Frozen.Vocabulary
