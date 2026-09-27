import Project.Gpt2QuantizedGroupedRows.ProjectionWord

namespace Project.Gpt2QuantizedGroupedRows.Projection
open Wasm Project.ProofKit PackedMemory LeanExe.Models.Gpt2.Quantized

theorem outputState_advance (params : List Wasm.Value) (valuePtr scalePtr : UInt64)
    (width outputWidth rows : Nat) (hParams : params.length = 11)
    (frame : Locals) (index : Nat) (hValid : frame.validIndex 30)
    (hState : OutputState params valuePtr scalePtr width outputWidth rows frame) :
    OutputState params valuePtr scalePtr width outputWidth rows
      (FixedArrayCopy.counterFrame frame 30 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hGroups, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr,
    hValueSize, hScaleCopyOwner, hScalePtr, hScaleSize, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [OutputState, FixedArrayCopy.counterFrame,
    Locals.set, hFrameParams, hParams, hLength, List.length_set, List.getElem?_set,
    Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hGroups, hValueOwner, hScaleOwner,
    hValueCopyOwner, hValuePtr, hValueSize, hScaleCopyOwner, hScalePtr, hScaleSize,
    hBytes, I64Values.set, hTyped, and_self]

theorem outputLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hValues : ByteArrayAt initial.mem valuePtr.toNat (quantizeRows input 64 (rows * (width / 64))).values)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input 64 (rows * (width / 64))).scales)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hBiasSize : withBias = true → biasOffset + outputWidth * 4 ≤ weights.size)
    (hWidth : 0 < width) (hMultiple : 64 ∣ width)
    (hFit : outputPtr.toNat + 4 * (rows * outputWidth) ≤ 2^32)
    (hMemory : outputPtr.toNat + 4 * (rows * outputWidth) ≤ initial.mem.pages * 65536)
    (hWeightSep : weightsPtr.toNat + weights.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (rows * outputWidth) ≤ weightsPtr.toNat)
    (hValueSep : valuePtr.toNat + rows * width ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (rows * outputWidth) ≤ valuePtr.toNat)
    (hScaleSep : scalePtr.toNat + 4 * (rows * (width / 64)) ≤ outputPtr.toNat ∨
      outputPtr.toNat + 4 * (rows * outputWidth) ≤ scalePtr.toNat)
    (hReady : PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) 0 outputPtr frame)
    (hState : OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result,
      PackedGenerateLoop.Ready 30 93 94 (rows * outputWidth) (rows * outputWidth) outputPtr result →
      OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
        width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows result →
      ByteArrayAt final.mem outputPtr.toNat
        (linearGroupedRows weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias) →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + 4 * (rows * outputWidth)) →
      wp «module» rest Q final result env) :
    wp «module» ((func8.drop 99).take 1 ++ rest) Q initial frame env := by
  have hCount : rows * outputWidth < UInt64.size := by
    change _ < 18446744073709551616
    omega
  rw [emitted_output]
  apply PackedGenerateLoop.program_spec
    (value := fun index => value weights input weightOffset scaleOffset biasOffset width outputWidth rows index withBias)
    (P := OutputState (parameters weightsPtr inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact outputState_advance _ valuePtr scalePtr width outputWidth rows rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact outputWord_spec env current weightsPtr inputPtr valuePtr scalePtr outputPtr weights input
      weightOffset scaleOffset biasOffset width outputWidth rows index withBias next
      (hWeights.writesRange hWrites hWeightSep)
      (hValues.writesRange hWrites (by simpa only [grouped_values_size input width rows hMultiple] using hValueSep))
      (hScales.writesRange hWrites (by simpa only [grouped_scales_size] using hScaleSep))
      hWeightSize hScaleSize hBiasSize hWidth hMultiple hCount hIndex hReady hState Q rest hNext
  · intro final result hReady hState hOutput hWrites
    exact hDone final result hReady hState (by simpa only [linearGroupedRows_eq] using hOutput) hWrites

#print axioms outputLoop_spec

end Project.Gpt2QuantizedGroupedRows.Projection
