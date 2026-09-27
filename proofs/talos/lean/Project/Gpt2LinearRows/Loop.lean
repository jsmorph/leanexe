import Project.Gpt2LinearRows.Word
import Project.Gpt2LinearRows.IndexBounds

namespace Project.Gpt2LinearRows

open Wasm Project.Common Project.ProofKit PackedMemory

set_option maxRecDepth 32768 in
theorem emitted_generation :
    (func1.drop 49).take 1 = PackedGenerateLoop.program 10 41 42 wordCode := rfl

theorem outputState_advance (weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows : Nat)
    (frame : Locals) (index : Nat) (hvalid : frame.validIndex 10)
    (hstate : OutputState weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows frame) :
    OutputState weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows
      (FixedArrayCopy.counterFrame frame 10 index hvalid) := by
  rcases hstate with ⟨hparams, hlength, hbytes⟩
  simp only [OutputState, FixedArrayCopy.counterFrame, Locals.set, hparams, parameters,
    hlength, List.length_cons, List.length_nil, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hbytes, and_self]

theorem generated_loop_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows : Nat) (frame : Locals)
    (hweights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hinput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hinputSize : rows * inputWidth * 4 ≤ input.size)
    (hweightSize : (weightOffset + inputWidth * outputWidth) * 4 ≤ weights.size)
    (hbiasSize : (biasOffset + outputWidth) * 4 ≤ weights.size)
    (hwidth : inputWidth < UInt64.size) (houtWidth : outputWidth < UInt64.size)
    (hfit : outputPtr.toNat + 4 * (rows * outputWidth) ≤ 2^32)
    (hmemory : outputPtr.toNat + 4 * (rows * outputWidth) ≤ initial.mem.pages * 65536)
    (hweightSep : weightsPtr.toNat + weights.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (rows * outputWidth) ≤ weightsPtr.toNat)
    (hinputSep : inputPtr.toNat + input.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (rows * outputWidth) ≤ inputPtr.toNat)
    (hready : PackedGenerateLoop.Ready 10 41 42 (rows * outputWidth) 0 outputPtr frame)
    (hstate : OutputState weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hdone : ∀ final result,
      PackedGenerateLoop.Ready 10 41 42 (rows * outputWidth) (rows * outputWidth) outputPtr result →
      OutputState weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows result →
      ByteArrayAt final.mem outputPtr.toNat
        (LeanExe.Models.Gpt2.linearRows weights input weightOffset biasOffset inputWidth outputWidth rows) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * (rows * outputWidth)) →
      wp «module» rest Q final result env) :
    wp «module» ((func1.drop 49).take 1 ++ rest) Q initial frame env := by
  rw [emitted_generation]
  apply PackedGenerateLoop.program_spec (value := fun index =>
    value weights input weightOffset biasOffset inputWidth outputWidth (index / outputWidth) (index % outputWidth))
    (P := OutputState weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows)
  · decide
  · decide
  · exact hready
  · exact hstate
  · exact hfit
  · exact hmemory
  · intro next index hvalid hstate
    exact outputState_advance weightsPtr inputPtr weights input weightOffset biasOffset
      inputWidth outputWidth rows next index hvalid hstate
  · intro current next index hindex hready hstate hwrites Q rest hnext
    have hout : 0 < outputWidth := Nat.pos_of_ne_zero (by intro h; simp [h] at hindex)
    apply word_spec env current weightsPtr inputPtr outputPtr weights input weightOffset biasOffset
      inputWidth outputWidth rows index next (hweights.writesRange hwrites hweightSep)
      (hinput.writesRange hwrites hinputSep)
    · exact fun inner hinner => input_index_bound rows inputWidth outputWidth index inner input.size hinputSize hindex hinner
    · exact fun inner hinner => weight_index_bound weightOffset inputWidth outputWidth index inner weights.size hweightSize hout hinner
    · exact bias_index_bound biasOffset outputWidth index weights.size hbiasSize hout
    · exact hwidth
    · exact houtWidth
    · omega
    · exact hindex
    · exact hready
    · exact hstate
    · exact hnext
  · intro final result hready hstate hbytes hwrites
    apply hdone final result hready hstate _ hwrites
    simpa only [linearRows_eq] using hbytes

#print axioms generated_loop_spec

end Project.Gpt2LinearRows
