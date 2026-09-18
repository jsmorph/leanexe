import Project.Gpt2CachedStep.LayerNorm.InversesLoop
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Gpt2CachedStep.LayerNorm
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def outputBody : Wasm.Program :=
  match (func20[147]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def outputWord : Wasm.Program := (outputBody.drop 12).take 141

def OutputState (params : List Wasm.Value) (meansOwner meansPtr inversesOwner inversesPtr : UInt64)
    (rows : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 74 ∧
  frame.locals[7]? = some (.i64 meansOwner) ∧
  frame.locals[8]? = some (.i64 meansPtr) ∧
  frame.locals[9]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧
  frame.locals[32]? = some (.i64 inversesOwner) ∧
  frame.locals[33]? = some (.i64 inversesPtr) ∧
  frame.locals[34]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧
  frame.locals[35]? = some (.i64 (UInt64.ofNat (4 * (rows * 768))))

set_option maxRecDepth 32768 in
theorem outputWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr meansOwner meansPtr inversesOwner inversesPtr outputPtr : UInt64)
    (weights input : ByteArray) (scaleOffset biasOffset rows index : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hMeans : ByteArrayAt initial.mem meansPtr.toNat (means input rows))
    (hInverses : ByteArrayAt initial.mem inversesPtr.toNat (inverses input rows))
    (hInputSize : rows * 768 * 4 ≤ input.size)
    (hScaleSize : (scaleOffset + 768) * 4 ≤ weights.size)
    (hBiasSize : (biasOffset + 768) * 4 ≤ weights.size)
    (hIndex : index < rows * 768)
    (hReady : PackedGenerateLoop.Ready 45 70 71 (rows * 768) index outputPtr frame)
    (hState : OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) meansOwner meansPtr inversesOwner inversesPtr rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 45 70 71 (rows * 768) index outputPtr result →
      OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
        scaleOffset biasOffset rows) meansOwner meansPtr inversesOwner inversesPtr rows result →
      wp «module» rest Q initial { result with values :=
        [.i64 (value weights input scaleOffset biasOffset rows index).toUInt64,
         .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (outputWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hMeansOwner, hMeansPtr, hMeansSize,
    hInversesOwner, hInversesPtr, hInversesSize, hBytes⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[36]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[61]? = some (.i64 (UInt64.ofNat (4 * (rows * 768)))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[62]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  have hIndex64 : index < UInt64.size := by
    have := hInput.1
    change index < 18446744073709551616
    omega
  have hDiv : UInt64.ofNat index / 768 = UInt64.ofNat (index / 768) :=
    (UInt64.ofNat_div hIndex64 (by decide : 768 < UInt64.size)).symm
  have hMod : UInt64.ofNat index % 768 = UInt64.ofNat (index % 768) :=
    (UInt64.ofNat_mod hIndex64 (by decide : 768 < UInt64.size)).symm
  have hScaleAdd := CheckedNatAdd.guard_of_fits scaleOffset (index % 768)
    (by have := hWeights.1; change scaleOffset + index % 768 < 18446744073709551616; omega)
  have hBiasAdd := CheckedNatAdd.guard_of_fits biasOffset (index % 768)
    (by have := hWeights.1; change biasOffset + index % 768 < 18446744073709551616; omega)
  have hScale : UInt64.ofNat scaleOffset + UInt64.ofNat (index % 768) =
      UInt64.ofNat (scaleOffset + index % 768) := by simp
  have hBias : UInt64.ofNat biasOffset + UInt64.ofNat (index % 768) =
      UInt64.ofNat (biasOffset + index % 768) := by simp
  simp only [outputWord, outputBody, func20, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env initial inputOwner inputPtr input index hInput (by omega)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro first returned ⟨out, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, hLength, hCounter, hMeansOwner, hMeansPtr, hMeansSize, hDiv]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by decide)])
  have hMeanRead := PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env first meansOwner meansPtr (means input rows) (index / 768) hMeans
      (by rw [means_size]; omega)
  rw [means_size] at hMeanRead
  refine wp_call_tw (hMeanRead.append_args rfl rfl rfl
    [.f32 (word input index), .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro second returned ⟨out, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, hLength, hCounter, hInversesOwner, hInversesPtr, hInversesSize, hDiv]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by decide)])
  have hInvRead := PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env second inversesOwner inversesPtr (inverses input rows) (index / 768) hInverses
      (by rw [inverses_size]; omega)
  rw [inverses_size] at hInvRead
  refine wp_call_tw (hInvRead.append_args rfl rfl rfl
    [.f32 (Wasm.IEEE32.sub (word input index) (word (means input rows) (index / 768))),
     .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro third returned ⟨out, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, hLength, hCounter, hMod]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hScaleAdd])])
  simp only [hScale]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env third weightsOwner weightsPtr weights (scaleOffset + index % 768) hWeights (by omega)).append_args
    rfl rfl rfl
    [.f32 (Wasm.IEEE32.mul (Wasm.IEEE32.sub (word input index) (word (means input rows) (index / 768)))
      (word (inverses input rows) (index / 768))), .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro fourth returned ⟨out, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, hLength, hCounter, hMod]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hBiasAdd])])
  simp only [hBias]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env fourth weightsOwner weightsPtr weights (biasOffset + index % 768) hWeights (by omega)).append_args
    rfl rfl rfl
    [.f32 (Wasm.IEEE32.mul
      (Wasm.IEEE32.mul (Wasm.IEEE32.sub (word input index) (word (means input rows) (index / 768)))
        (word (inverses input rows) (index / 768))) (word weights (scaleOffset + index % 768))),
     .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final returned ⟨out, rfl, rfl, rfl⟩
  wp_packed_frame [hParams, hLength, hCounter]
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 45 70 71 (rows * 768) index outputPtr result ∧
      OutputState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
        scaleOffset biasOffset rows) meansOwner meansPtr inversesOwner inversesPtr rows result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (value weights input scaleOffset biasOffset rows index).toUInt64,
      .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer, true_and]
    · simp only [OutputState, parameters, hLength, List.length_set, List.getElem?_set,
        Nat.reduceEqDiff, reduceIte, hMeansOwner, hMeansPtr, hMeansSize,
        hInversesOwner, hInversesPtr, hInversesSize, hBytes, and_self]
  · intro result h
    exact hNext result h.1 h.2

#print axioms outputWord_spec

end Project.Gpt2CachedStep.LayerNorm
