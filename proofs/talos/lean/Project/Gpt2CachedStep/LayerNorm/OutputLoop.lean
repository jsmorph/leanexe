import Project.Gpt2CachedStep.LayerNorm.OutputWord

namespace Project.Gpt2CachedStep.LayerNorm
open Wasm Project.ProofKit PackedMemory

set_option maxRecDepth 32768 in
theorem emitted_output : (func20.drop 147).take 1 =
    PackedGenerateLoop.program 45 70 71 outputWord := rfl

theorem outputState_advance (params : List Wasm.Value)
    (meansOwner meansPtr inversesOwner inversesPtr : UInt64) (rows : Nat)
    (hParams : params.length = 9) (frame : Locals) (index : Nat) (hValid : frame.validIndex 45)
    (hState : OutputState params meansOwner meansPtr inversesOwner inversesPtr rows frame) :
    OutputState params meansOwner meansPtr inversesOwner inversesPtr rows
      (FixedArrayCopy.counterFrame frame 45 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hMeansOwner, hMeansPtr, hMeansSize,
    hInversesOwner, hInversesPtr, hInversesSize, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [OutputState, FixedArrayCopy.counterFrame, Locals.set, hFrameParams, hParams,
    hLength, List.length_set, List.getElem?_set, Nat.reduceSub, Nat.reduceLT,
    Nat.reduceEqDiff, reduceIte, hMeansOwner, hMeansPtr, hMeansSize,
    hInversesOwner, hInversesPtr, hInversesSize, hBytes, I64Values.set, hTyped, and_self]

set_option maxRecDepth 32768 in
theorem outputLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr meansOwner meansPtr inversesOwner inversesPtr outputPtr : UInt64)
    (weights input : ByteArray) (scaleOffset biasOffset rows : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hMeans : ByteArrayAt initial.mem meansPtr.toNat (means input rows))
    (hInverses : ByteArrayAt initial.mem inversesPtr.toNat (inverses input rows))
    (hInputSize : rows * 768 * 4 ≤ input.size)
    (hScaleSize : (scaleOffset + 768) * 4 ≤ weights.size)
    (hBiasSize : (biasOffset + 768) * 4 ≤ weights.size)
    (hFit : outputPtr.toNat + 4 * (rows * 768) ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * (rows * 768) ≤ initial.mem.pages * 65536)
    (hWeightsSep : weightsPtr.toNat + weights.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (rows * 768) ≤ weightsPtr.toNat)
    (hInputSep : inputPtr.toNat + input.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (rows * 768) ≤ inputPtr.toNat)
    (hMeansSep : meansPtr.toNat + (means input rows).size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (rows * 768) ≤ meansPtr.toNat)
    (hInversesSep : inversesPtr.toNat + (inverses input rows).size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (rows * 768) ≤ inversesPtr.toNat)
    (hReady : PackedGenerateLoop.Ready 45 70 71 (rows * 768) 0 outputPtr frame)
    (hState : OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) meansOwner meansPtr inversesOwner inversesPtr rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result, PackedGenerateLoop.Ready 45 70 71 (rows * 768) (rows * 768) outputPtr result →
      OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
        scaleOffset biasOffset rows) meansOwner meansPtr inversesOwner inversesPtr rows result →
      ByteArrayAt final.mem outputPtr.toNat (LeanExe.Models.Gpt2.layerNorm weights input scaleOffset biasOffset rows) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * (rows * 768)) →
      wp «module» rest Q final result env) :
    wp «module» ((func20.drop 147).take 1 ++ rest) Q initial frame env := by
  rw [emitted_output]
  apply PackedGenerateLoop.program_spec (value := value weights input scaleOffset biasOffset rows)
    (P := OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) meansOwner meansPtr inversesOwner inversesPtr rows)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact outputState_advance _ meansOwner meansPtr inversesOwner inversesPtr rows rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact outputWord_spec env current weightsOwner inputOwner weightsPtr inputPtr meansOwner meansPtr
      inversesOwner inversesPtr outputPtr weights input scaleOffset biasOffset rows index next
      (hWeights.writesRange hWrites hWeightsSep) (hInput.writesRange hWrites hInputSep)
      (hMeans.writesRange hWrites hMeansSep) (hInverses.writesRange hWrites hInversesSep)
      hInputSize hScaleSize hBiasSize hIndex hReady hState Q rest hNext
  · intro final result hReady hState hBytes hWrites
    apply hDone final result hReady hState _ hWrites
    simpa only [layerNorm_eq] using hBytes

#print axioms outputLoop_spec

end Project.Gpt2CachedStep.LayerNorm
