import Project.Gpt2QuantizedCached.Embedding.Word

namespace Project.Gpt2QuantizedCached.Embedding
open Wasm Project.Common Project.ProofKit PackedMemory LeanExe.Models.Gpt2.Quantized

theorem state_advance (params : List Wasm.Value) (hParams : params.length = 5)
    (weights : ByteArray) (token : UInt32) (frame : Locals) (index : Nat) (hValid : frame.validIndex 7)
    (hState : State params weights token frame) :
    State params weights token (FixedArrayCopy.counterFrame frame 7 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hScale, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [State, FixedArrayCopy.counterFrame, Locals.set,
    hFrameParams, hParams, hLength, List.length_set, List.getElem?_set, Nat.reduceSub,
    Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hScale, hBytes, I64Values.set, hTyped, and_self]

theorem loop_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr outputPtr : UInt64) (weights : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hTokenSize : tokenWeightOffset + token.toNat * 768 + 768 ≤ weights.size)
    (hPositionSize : positionOffset + (position * 768 + 768) * 4 ≤ weights.size)
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (hFit : outputPtr.toNat + 3072 ≤ 2^32)
    (hMemory : outputPtr.toNat + 3072 ≤ initial.mem.pages * 65536)
    (hSep : ptr.toNat + weights.size ≤ outputPtr.toNat ∨ outputPtr.toNat + 3072 ≤ ptr.toNat)
    (hReady : PackedGenerateLoop.Ready 7 12 13 768 0 outputPtr frame)
    (hState : State (parameters owner ptr weights token position) weights token frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 7 12 13 768 768 outputPtr result →
      State (parameters owner ptr weights token position) weights token result →
      ByteArrayAt final.mem outputPtr.toNat (embedding weights token position) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 3072) →
      wp «module» rest Q final result env) :
    wp «module» ((func30.drop 70).take 1 ++ rest) Q initial frame env := by
  rw [emitted_loop]
  apply PackedGenerateLoop.program_spec (value := value weights token position)
    (P := State (parameters owner ptr weights token position) weights token)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact state_advance _ rfl weights token next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact word_spec env current owner ptr outputPtr weights token position
      index next (hWeights.writesRange hWrites hSep) hTokenSize hPositionSize hToken hPosition hIndex hReady hState Q rest hNext
  · simpa only [← source_eq] using hDone

#print axioms loop_spec

end Project.Gpt2QuantizedCached.Embedding
