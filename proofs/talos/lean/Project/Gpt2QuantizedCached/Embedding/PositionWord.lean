import Project.Gpt2QuantizedCached.Embedding.WordState

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Embedding
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem position_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr outputPtr : UInt64) (weights : ByteArray)
    (token : UInt32) (position index : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hPositionSize : positionOffset + (position * 768 + 768) * 4 ≤ weights.size)
    (hPosition : position < 128) (hIndex : index < 768)
    (hReady : PackedGenerateLoop.Ready 7 12 13 768 index outputPtr frame)
    (hState : State (parameters owner ptr weights token position) weights token frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 7 12 13 768 index outputPtr result →
      State (parameters owner ptr weights token position) weights token result →
      wp «module» rest Q initial { result with values :=
        [.i64 (value weights token position index).toUInt64,
          .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (positionCode ++ rest) Q initial
      { frame with values := [.f32 (tokenValue weights token index),
        .i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hScale, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[2]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[7]? = some (.i64 3072) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[8]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  have hPositionMul : ¬ (-1 : UInt64) / 768 < UInt64.ofNat position := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by
      change position < 18446744073709551616; omega)]
    change ¬ 24019198012642645 < position
    omega
  have hByteMul : ¬ (-1 : UInt64) / 4 < UInt64.ofNat (position * 768 + index) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by
      change position * 768 + index < 18446744073709551616; omega)]
    change ¬ 4611686018427387903 < position * 768 + index
    omega
  have hPositionChannel := CheckedNatAdd.guard_of_fits (position * 768) index
    (by change position * 768 + index < 18446744073709551616; omega)
  have hPositionAdd := CheckedNatAdd.guard_of_fits positionOffset ((position * 768 + index) * 4)
    (by change 38798436 + (position * 768 + index) * 4 < 18446744073709551616; omega)
  simp only [positionCode, wordCode, loopBody, func30, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.length_cons, List.length_nil, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_call_tw ((Layout.positionOffset_exact env initial).append_args rfl rfl rfl
    [.f32 (Wasm.IEEE32.mul (Wasm.IEEE32.convertI32S (LeanExe.Signed32.extend8Bits
      weights[tokenWeightOffset + token.toNat * 768 + index]!.toUInt32)) (scale weights token)),
      .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength, hCounter]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hPositionMul)]
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_mul]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hPositionChannel)]
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hByteMul)]
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_mul]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hPositionAdd)]
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_add]
  apply PackedWordAccess.guard_spec «module» env initial _ ptr weights
    (positionOffset + (position * 768 + index) * 4) 14 15 16
    [.f32 (Wasm.IEEE32.mul (Wasm.IEEE32.convertI32S (LeanExe.Signed32.extend8Bits
      weights[tokenWeightOffset + token.toNat * 768 + index]!.toUInt32)) (scale weights token)),
      .i32 (PackedGenerateLoop.address outputPtr index)] hWeights (by omega)
  · simp [Locals.get, hLength]
  · simp [Locals.get, hLength]
  · simp [Locals.get, hLength, UInt64.ofNat_add, UInt64.ofNat_mul]
  · simp [UInt64.ofNat_add, UInt64.ofNat_mul]
  wp_packed_frame [hParams, hLength]
  simp only [value, F32Add.add_eq, F32Mul.mul_eq, F32Convert.ofInt32Bits_eq] at hNext
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 7 12 13 768 index outputPtr result ∧
      State (parameters owner ptr weights token position) weights token result)
    (R := fun result => wp «module» rest Q initial result env) (values := _) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer,
        show UInt64.ofNat (4 * 768) = 3072 from rfl, true_and]
    · simp only [State, parameters]
      refine ⟨by simp only [UInt64.ofNat_uInt32ToNat], ?_, ?_, ?_, ?_⟩
      · simp only [List.length_set, hLength]
      · simp only [List.getElem?_set, Nat.reduceEqDiff, reduceIte, hScale]
      · simp only [List.getElem?_set, Nat.reduceEqDiff, reduceIte, hBytes]
      · repeat first | apply I64Values.set | exact hTyped
  · intro result h
    exact hNext result h.1 h.2


#print axioms position_spec
end Project.Gpt2QuantizedCached.Embedding
