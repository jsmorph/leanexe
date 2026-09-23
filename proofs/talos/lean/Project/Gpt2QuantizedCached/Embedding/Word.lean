import Project.Gpt2QuantizedCached.Embedding.TokenWord
import Project.Gpt2QuantizedCached.Embedding.PositionWord

namespace Project.Gpt2QuantizedCached.Embedding
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem word_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr outputPtr : UInt64) (weights : ByteArray)
    (token : UInt32) (position index : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hTokenSize : tokenWeightOffset + token.toNat * 768 + 768 ≤ weights.size)
    (hPositionSize : positionOffset + (position * 768 + 768) * 4 ≤ weights.size)
    (hToken : token.toNat < 50257) (hPosition : position < 128) (hIndex : index < 768)
    (hReady : PackedGenerateLoop.Ready 7 12 13 768 index outputPtr frame)
    (hState : State (parameters owner ptr weights token position) weights token frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 7 12 13 768 index outputPtr result →
      State (parameters owner ptr weights token position) weights token result →
      wp «module» rest Q initial { result with values :=
        [.i64 (value weights token position index).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (wordCode ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rw [word_parts, List.append_assoc]
  apply token_spec env initial owner ptr outputPtr weights token position index frame
    hWeights hTokenSize hToken hIndex hReady hState
  intro next hNextReady hNextState
  exact position_spec env initial owner ptr outputPtr weights token position index next
    hWeights hPositionSize hPosition hIndex hNextReady hNextState Q rest hNext

#print axioms word_spec
end Project.Gpt2QuantizedCached.Embedding
