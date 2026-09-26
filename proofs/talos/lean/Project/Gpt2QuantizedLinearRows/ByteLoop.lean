import Project.Gpt2QuantizedLinearRows.ByteWord

namespace Project.Gpt2QuantizedLinearRows.QuantizeRows
open Wasm Project.ProofKit PackedMemory LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

theorem byteState_advance (params : List Wasm.Value) (scalePtr : UInt64) (width rows : Nat)
    (hParams : params.length = 5) (frame : Locals) (index : Nat) (hValid : frame.validIndex 17)
    (hState : ByteState params scalePtr width rows frame) :
    ByteState params scalePtr width rows (FixedArrayCopy.counterFrame frame 17 index hValid) := by
  rcases hState with ⟨hFrameParams, hLength, hOwner, hPointer, hScales, hBytes, hTyped⟩
  simp (config := { maxDischargeDepth := 64 }) only [ByteState, FixedArrayCopy.counterFrame,
    Locals.set, hFrameParams, hParams, hLength, List.length_set, List.getElem?_set,
    Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hOwner, hPointer, hScales,
    hBytes, I64Values.set, hTyped, and_self]

theorem byteLoop_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr scalePtr outputPtr : UInt64) (input : ByteArray) (width rows : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem ptr.toNat input)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input width rows).scales)
    (hSize : rows * width * 4 ≤ input.size)
    (hFit : outputPtr.toNat + rows * width ≤ 2^32)
    (hMemory : outputPtr.toNat + rows * width ≤ initial.mem.pages * 65536)
    (hInputSep : ptr.toNat + input.size ≤ outputPtr.toNat ∨
      outputPtr.toNat + rows * width ≤ ptr.toNat)
    (hScaleSep : scalePtr.toNat + 4 * rows ≤ outputPtr.toNat ∨
      outputPtr.toNat + rows * width ≤ scalePtr.toNat)
    (hReady : PackedByteGenerateLoop.Ready 17 40 41 (rows * width) 0 outputPtr frame)
    (hState : ByteState (parameters owner ptr input width rows) scalePtr width rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final result,
      PackedByteGenerateLoop.Ready 17 40 41 (rows * width) (rows * width) outputPtr result →
      ByteState (parameters owner ptr input width rows) scalePtr width rows result →
      ByteArrayAt final.mem outputPtr.toNat (quantizeRows input width rows).values →
      Memory.WritesRange initial final outputPtr.toNat (outputPtr.toNat + rows * width) →
      wp «module» rest Q final result env) :
    wp «module» ((func3.drop 98).take 1 ++ rest) Q initial frame env := by
  rw [emitted_bytes]
  apply PackedByteGenerateLoop.program_spec
    (value := fun index => quantizeValue (word input index)
      (word (quantizeRows input width rows).scales (index / width)))
    (P := ByteState (parameters owner ptr input width rows) scalePtr width rows)
  · decide
  · decide
  · exact hReady
  · exact hState
  · exact hFit
  · exact hMemory
  · intro next index hValid hState
    exact byteState_advance _ scalePtr width rows rfl next index hValid hState
  · intro current next index hIndex hReady hState hWrites Q rest hNext
    exact byteWord_spec env current owner ptr scalePtr outputPtr input width rows index next
      (hInput.writesRange hWrites hInputSep)
      (hScales.writesRange hWrites (by simpa only [quantized_scales_size] using hScaleSep))
      hSize hIndex hReady hState Q rest hNext
  · exact hDone

#print axioms byteLoop_spec

end Project.Gpt2QuantizedLinearRows.QuantizeRows
