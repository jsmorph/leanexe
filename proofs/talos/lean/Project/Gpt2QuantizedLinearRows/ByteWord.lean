import Project.Gpt2QuantizedLinearRows.ScaleLoop
import Project.Gpt2QuantizedLinearRows.Scalars
import Project.ProofKit.PackedByteGenerateLoop

namespace Project.Gpt2QuantizedLinearRows.QuantizeRows
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized

def byteBody : Wasm.Program :=
  match (func3[98]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def byteWord : Wasm.Program := (byteBody.drop 12).take (byteBody.length - 19)

theorem emitted_bytes : (func3.drop 98).take 1 = PackedByteGenerateLoop.program 17 40 41 byteWord := rfl

def ByteState (params : List Wasm.Value) (scalePtr : UInt64) (width rows : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 43 ∧
  frame.locals[8]? = some (.i64 scalePtr) ∧ frame.locals[9]? = some (.i64 scalePtr) ∧
  frame.locals[10]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧
  frame.locals[11]? = some (.i64 (UInt64.ofNat (rows * width))) ∧ I64Values frame.locals

set_option maxRecDepth 16384 in
theorem byteWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr scalePtr outputPtr : UInt64) (input : ByteArray) (width rows index : Nat) (frame : Locals)
    (hInput : ByteArrayAt initial.mem ptr.toNat input)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input width rows).scales)
    (hSize : rows * width * 4 ≤ input.size) (hIndex : index < rows * width)
    (hReady : PackedByteGenerateLoop.Ready 17 40 41 (rows * width) index outputPtr frame)
    (hState : ByteState (parameters owner ptr input width rows) scalePtr width rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedByteGenerateLoop.Ready 17 40 41 (rows * width) index outputPtr result →
      ByteState (parameters owner ptr input width rows) scalePtr width rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (quantizeValue (word input index)
          (word (quantizeRows input width rows).scales (index / width))).toUInt64,
          .i32 (PackedByteGenerateLoop.address outputPtr index)] } env) :
    wp «module» (byteWord ++ rest) Q initial
      { frame with values := [.i32 (PackedByteGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hScaleOwner, hScalePtr, hScaleSize, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[12]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[35]? = some (.i64 (UInt64.ofNat (rows * width))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[36]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  have hWidth : 0 < width := by nlinarith
  have hRows : 0 < rows := by nlinarith
  have hfit := hInput.1
  have hi64 : index < UInt64.size := by change index < 18446744073709551616; omega
  have hw64 : width < UInt64.size := by
    change width < 18446744073709551616
    nlinarith
  have hwne : UInt64.ofNat width ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hw64] at this
    change width = 0 at this
    omega
  have hdiv : UInt64.ofNat index / UInt64.ofNat width = UInt64.ofNat (index / width) := by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' hi64, UInt64.toNat_ofNat_of_lt' hw64,
      UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (Nat.div_le_self ..) hi64)]
  have hRow : index / width < rows := (Nat.div_lt_iff_lt_mul hWidth).mpr hIndex
  simp only [byteWord, byteBody, func3, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.drop, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_call_tw ((PackedWordRead.exact «module» 0 (some 0) rfl rfl
    env initial owner ptr input index hInput (by omega)).append_args
    rfl rfl rfl [.i32 (PackedByteGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength, hCounter, hScaleOwner, hScalePtr, hScaleSize]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hwne)]
  wp_packed_frame [hParams, hLength, hCounter, hScaleOwner, hScalePtr, hScaleSize, hdiv, hwne]
  have hRead := PackedWordRead.exact «module» 0 (some 0) rfl rfl
    env initial scalePtr scalePtr (quantizeRows input width rows).scales (index / width)
    hScales (by rw [quantized_scales_size]; omega)
  simp only [quantized_scales_size] at hRead
  refine wp_call_tw (hRead.append_args rfl rfl rfl [.i32 (PackedByteGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength, hCounter, hScaleOwner, hScalePtr, hScaleSize]
  refine wp_call_tw ((quantizeValue_exact env initial (word input index)
    (word (quantizeRows input width rows).scales (index / width))).append_args
    rfl rfl rfl [.i32 (PackedByteGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, hFinal, rfl⟩
  subst final
  apply Frame.of_withValues
    (P := fun result => PackedByteGenerateLoop.Ready 17 40 41 (rows * width) index outputPtr result ∧
      ByteState (parameters owner ptr input width rows) scalePtr width rows result)
    (R := fun result => wp «module» rest Q initial result env)
    (values := [.i64 (quantizeValue (word input index)
      (word (quantizeRows input width rows).scales (index / width))).toUInt64,
      .i32 (PackedByteGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedByteGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
    · simp (config := { maxDischargeDepth := 64 }) only [ByteState, parameters, hLength,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte, hScaleOwner,
        hScalePtr, hScaleSize, hBytes, I64Values.set, hTyped, and_self]
  · intro result h
    exact hNext result h.1 h.2

#print axioms byteWord_spec

end Project.Gpt2QuantizedLinearRows.QuantizeRows
