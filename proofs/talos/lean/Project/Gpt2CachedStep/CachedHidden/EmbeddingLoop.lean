import Project.Gpt2CachedStep.CachedHidden.EmbeddingWord

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Common Project.ProofKit PackedMemory LeanExe.Models.Gpt2

theorem embeddingState_advance (params : List Wasm.Value) (hParams : params.length = 8)
    (frame : Locals) (index : Nat) (hValid : frame.validIndex 9)
    (hState : EmbeddingState params frame) :
    EmbeddingState params (FixedArrayCopy.counterFrame frame 9 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [EmbeddingState, FixedArrayCopy.counterFrame, Locals.set,
    hFrameParams, hParams, hLength, List.length_set, List.getElem?_set, Nat.reduceSub,
    Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hBytes, I64Values.set, hTyped, and_self]

theorem embeddingLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr cacheOwner cachePtr outputPtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hTokenSize : 4 * (token.toNat * 768 + 768) ≤ weights.size)
    (hPositionSize : 4 * (positionOffset + position * 768 + 768) ≤ weights.size)
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (hFit : outputPtr.toNat + 3072 ≤ 2^32)
    (hMemory : outputPtr.toNat + 3072 ≤ initial.mem.pages * 65536)
    (hSep : weightsPtr.toNat + weights.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 3072 ≤ weightsPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 9 103 104 768 0 outputPtr frame)
    (hState : EmbeddingState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 9 103 104 768 768 outputPtr result →
      EmbeddingState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) result →
      ByteArrayAt final.mem outputPtr.toNat (embedding weights token position) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 3072) →
      wp «module» rest Q final result env) :
    wp «module» ((func36.drop 42).take 1 ++ rest) Q initial frame env := by
  rw [emitted_embedding]
  apply PackedGenerateLoop.program_spec (value := fun index =>
    LeanExe.Float32.addBits (word weights (token.toNat * 768 + index))
      (word weights (positionOffset + position * 768 + index)))
    (P := EmbeddingState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position))
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact embeddingState_advance _ rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact embeddingWord_spec env current weightsOwner weightsPtr cacheOwner cachePtr outputPtr weights cache token position
      index next (hWeights.writesRange hWrites hSep) hTokenSize hPositionSize hToken hPosition hIndex hReady hState Q rest hNext
  · exact hDone

#print axioms embeddingLoop_spec

end Project.Gpt2CachedStep.CachedHidden
