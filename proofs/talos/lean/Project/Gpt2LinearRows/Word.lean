import Project.Gpt2LinearRows.DotStep
import Project.ProofKit.PackedGenerateLoop

namespace Project.Gpt2LinearRows

open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def wordCode : Wasm.Program := (outerBody.drop 12).take 64

set_option maxRecDepth 32768 in
theorem emitted_dot : wordCode = wordCode.take 28 ++ RangeFoldLoop.program 43 44 dotStep ++ wordCode.drop 29 := rfl

def OutputState (weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows : Nat) (frame : Locals) : Prop :=
  frame.params = parameters weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows ∧
  frame.locals.length = 48 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth))))

set_option maxRecDepth 32768 in
theorem word_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr inputPtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows index : Nat) (frame : Locals)
    (hweights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hinput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hinputIndex : ∀ inner, inner < inputWidth →
      ((index / outputWidth) * inputWidth + inner) * 4 + 4 ≤ input.size)
    (hweightIndex : ∀ inner, inner < inputWidth →
      (weightOffset + inner * outputWidth + index % outputWidth) * 4 + 4 ≤ weights.size)
    (hbiasIndex : (biasOffset + index % outputWidth) * 4 + 4 ≤ weights.size)
    (hwidth : inputWidth < UInt64.size) (houtWidth : outputWidth < UInt64.size)
    (hcount : 4 * (rows * outputWidth) ≤ 2^32) (hindex : index < rows * outputWidth)
    (hready : PackedGenerateLoop.Ready 10 41 42 (rows * outputWidth) index outputPtr frame)
    (hstate : OutputState weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result,
      PackedGenerateLoop.Ready 10 41 42 (rows * outputWidth) index outputPtr result →
      OutputState weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (value weights input weightOffset biasOffset inputWidth outputWidth
          (index / outputWidth) (index % outputWidth)).toUInt64,
         .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (wordCode ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hstate with ⟨hparams, hlength, hbyteLength⟩
  simp only [parameters] at hparams
  have hcounter : frame.locals[1]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hlengthLocal : frame.locals[32]? = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth)))) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2.1
  have hpointerLocal : frame.locals[33]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2.2.1
  have hindex64 : index < UInt64.size := by change index < 18446744073709551616; omega
  have houtPositive : 0 < outputWidth := Nat.pos_of_ne_zero (by intro h; simp [h] at hindex)
  have hcolumn := Nat.mod_lt index houtPositive
  have houtNonzero : UInt64.ofNat outputWidth ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' houtWidth] at this
    change outputWidth = 0 at this
    omega
  have hdiv : UInt64.ofNat index / UInt64.ofNat outputWidth = UInt64.ofNat (index / outputWidth) :=
    (UInt64.ofNat_div hindex64 houtWidth).symm
  have hmod : UInt64.ofNat index % UInt64.ofNat outputWidth = UInt64.ofNat (index % outputWidth) :=
    (UInt64.ofNat_mod hindex64 houtWidth).symm
  have hweightSize := hweights.1
  have hBiasAdd := CheckedNatAdd.guard_of_fits biasOffset (index % outputWidth)
    (by change biasOffset + index % outputWidth < 18446744073709551616; omega)
  have hbiasAddr : UInt64.ofNat biasOffset + UInt64.ofNat (index % outputWidth) =
      UInt64.ofNat (biasOffset + index % outputWidth) := by simp
  rw [emitted_dot]
  simp only [List.append_assoc]
  simp only [wordCode, outerBody, func1, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.drop, List.cons_append, List.nil_append]
  repeat' first
    | wp_packed_frame [hparams, hlength, hcounter, houtNonzero, hdiv, hmod]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [houtNonzero])])
  apply RangeFoldLoop.program_spec_with_stack (values := [.i32 (PackedGenerateLoop.address outputPtr index)])
    (count := inputWidth) (P := fun inner => Accumulator weightsPtr inputPtr weights input
      weightOffset biasOffset inputWidth outputWidth rows (index / outputWidth) (index % outputWidth) inner frame)
  · exact hwidth
  · simp [RangeFoldLoop.Ready, Locals.get, hlength]
  · simp [Accumulator, parameters, Saved, hlength]
  · intro inner next hinner hinnerReady hacc Q rest hnext
    exact dotStep_spec env initial weightsPtr inputPtr weights input weightOffset biasOffset
      inputWidth outputWidth rows (index / outputWidth) (index % outputWidth) inner frame next
      [.i32 (PackedGenerateLoop.address outputPtr index)] hweights hinput (hinputIndex inner hinner)
      (hweightIndex inner hinner) hwidth houtWidth hcolumn hinner hinnerReady hacc Q rest hnext
  · intro result hinnerReady hacc
    rcases hacc with ⟨hresultParams, hresultLength, hrow, hcol, htotal, hstride, hsaved⟩
    simp only [parameters] at hresultParams
    repeat' first
      | wp_packed_frame [hresultParams, hresultLength, hcol, htotal, hinnerReady.1]
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hBiasAdd])])
    simp only [hbiasAddr]
    refine wp_call_tw ((PackedWordRead.exact «module» 0 (some 0) rfl rfl
      env initial 0 weightsPtr weights (biasOffset + index % outputWidth) hweights hbiasIndex).append_args
        rfl rfl rfl [.f32 (dotPrefix weights input weightOffset inputWidth outputWidth
          (index / outputWidth) (index % outputWidth) inputWidth),
          .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
    rintro final values ⟨returned, rfl, rfl, rfl⟩
    wp_packed_frame [hresultParams, hresultLength, hcol, htotal, hinnerReady.1]
    apply Frame.of_withValues
      (P := fun result => PackedGenerateLoop.Ready 10 41 42 (rows * outputWidth) index outputPtr result ∧
        OutputState weightsPtr inputPtr weights input weightOffset biasOffset inputWidth outputWidth rows result)
      (R := fun result => wp «module» rest Q final result env)
      (values := [.i64 (value weights input weightOffset biasOffset inputWidth outputWidth
        (index / outputWidth) (index % outputWidth)).toUInt64, .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
    · constructor
      · rcases hsaved with ⟨hs0, hs1, hs32, hs33⟩
        simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
          hresultLength, List.length_set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
          Nat.reduceEqDiff, hs1, hs32, hs33, hcounter, hlengthLocal, hpointerLocal, true_and]
      · simpa only [OutputState, parameters, hresultLength, List.length_set, List.getElem?_set,
          Nat.reduceLT, Nat.reduceEqDiff, reduceIte, true_and] using hsaved.1.trans hbyteLength
    · intro result h
      exact hnext result h.1 h.2

#print axioms word_spec

end Project.Gpt2LinearRows
