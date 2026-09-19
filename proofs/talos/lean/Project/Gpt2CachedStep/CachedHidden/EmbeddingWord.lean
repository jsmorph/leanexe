import Project.Gpt2CachedStep.CachedHidden.Source
import Project.Gpt2CachedStep.Layout
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.PackedWordRead
import Project.ProofKit.F32Add
import Project.ProofKit.PackedGenerateLoop
import Project.ProofKit.I64Frame

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def parameters (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) : List Wasm.Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
   .i64 cacheOwner, .i64 cachePtr, .i64 (UInt64.ofNat cache.size),
   .i64 (UInt64.ofNat token.toNat), .i64 (UInt64.ofNat position)]

def embeddingWord : Wasm.Program :=
  [.localGet 0, .localSet 10, .localGet 1, .localSet 11, .localGet 2, .localSet 12,
   .localGet 6, .localSet 108, .constI64 768, .localSet 109] ++
  CheckedNatMul.program 108 109 ++
  [.localSet 105, .localGet 9, .localSet 106,
   .localGet 105, .localGet 106, .addI64, .localTee 107, .localGet 105, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 107] [] [.i64], .localSet 13,
   .localGet 10, .localGet 11, .localGet 12, .localGet 13, .call 17,
   .wrapI64, .f32ReinterpretI32,
   .localGet 0, .localSet 14, .localGet 1, .localSet 15, .localGet 2, .localSet 16,
   .call 1, .localSet 108, .localGet 7, .localSet 111, .constI64 768, .localSet 112] ++
  CheckedNatMul.program 111 112 ++
  [.localSet 109, .localGet 108, .localGet 109, .addI64, .localTee 110, .localGet 108, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 110] [] [.i64], .localSet 105,
   .localGet 9, .localSet 106,
   .localGet 105, .localGet 106, .addI64, .localTee 107, .localGet 105, .ltUI64,
   .iff 0 1 [.unreachable] [.localGet 107] [] [.i64], .localSet 17,
   .localGet 14, .localGet 15, .localGet 16, .localGet 17, .call 17,
   .wrapI64, .f32ReinterpretI32, .f32Add, .i32ReinterpretF32, .extendUI32]

set_option maxRecDepth 32768 in
theorem emitted_embedding : (func36.drop 42).take 1 =
    PackedGenerateLoop.program 9 103 104 embeddingWord := rfl

def EmbeddingState (params : List Wasm.Value) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 119 ∧
  frame.locals[0]? = some (.i64 3072) ∧ I64Values frame.locals

theorem embeddingWord_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr cacheOwner cachePtr outputPtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position index : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hTokenSize : 4 * (token.toNat * 768 + 768) ≤ weights.size)
    (hPositionSize : 4 * (positionOffset + position * 768 + 768) ≤ weights.size)
    (hToken : token.toNat < 50257) (hPosition : position < 128) (hIndex : index < 768)
    (hReady : PackedGenerateLoop.Ready 9 103 104 768 index outputPtr frame)
    (hState : EmbeddingState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 9 103 104 768 index outputPtr result →
      EmbeddingState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) result →
      wp «module» rest Q initial { result with values :=
        [.i64 (LeanExe.Float32.addBits (word weights (token.toNat * 768 + index))
          (word weights (positionOffset + position * 768 + index))).toUInt64,
         .i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (embeddingWord ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rcases hState with ⟨hParams, hLength, hBytes, hTyped⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[1]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hLengthLocal : frame.locals[95]? = some (.i64 3072) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.1
  have hPointer : frame.locals[96]? = some (.i64 outputPtr) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2.2.1
  have hToken64 : token.toNat < UInt64.size := by change _ < 18446744073709551616; omega
  have hPosition64 : position < UInt64.size := by change _ < 18446744073709551616; omega
  have hTokenAdd := CheckedNatAdd.guard_of_fits (token.toNat * 768) index
    (by change _ < 18446744073709551616; omega)
  have hTokenIndex : token.toUInt64 * 768 + UInt64.ofNat index = UInt64.ofNat (token.toNat * 768 + index) := by
    simp [UInt64.ofNat_add, UInt64.ofNat_mul]
  have hPositionAdd := CheckedNatAdd.guard_of_fits positionOffset (position * 768)
    (by change 38597376 + position * 768 < 18446744073709551616; omega)
  have hChannelAdd := CheckedNatAdd.guard_of_fits (positionOffset + position * 768) index
    (by change 38597376 + position * 768 + index < 18446744073709551616; omega)
  have hPositionIndex : UInt64.ofNat positionOffset + UInt64.ofNat position * 768 + UInt64.ofNat index =
      UInt64.ofNat (positionOffset + position * 768 + index) := by
    simp [UInt64.ofNat_add, UInt64.ofNat_mul]
  simp only [embeddingWord, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hCounter]
  apply CheckedNatMul.program_spec 108 109 «module» env initial _
    (UInt64.ofNat token.toNat) 768 [.i32 (PackedGenerateLoop.address outputPtr index)]
  · rfl
  · simp [Locals.get, hLength]
  · simp [Locals.get, hLength]
  · rw [UInt64.toNat_ofNat_of_lt' hToken64]
    change token.toNat * 768 < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_mul]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hTokenAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  simp only [hTokenIndex]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial
    weightsOwner weightsPtr weights (token.toNat * 768 + index) hWeights (by omega)).append_args
    rfl rfl rfl [.i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParams, hLength]
  refine wp_call_tw ((Layout.positionOffset_exact env final).append_args rfl rfl rfl
    [.f32 (word weights (token.toNat * 768 + index)), .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParams, hLength]
  apply CheckedNatMul.program_spec 111 112 «module» env final _
    (UInt64.ofNat position) 768
    [.f32 (word weights (token.toNat * 768 + index)), .i32 (PackedGenerateLoop.address outputPtr index)]
  · rfl
  · simp [Locals.get, hLength]
  · simp [Locals.get, hLength]
  · rw [UInt64.toNat_ofNat_of_lt' hPosition64]
    change position * 768 < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_mul]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hPositionAdd)]
  wp_packed_frame [hParams, hLength, hCounter, ← UInt64.ofNat_add]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hChannelAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  simp only [hPositionIndex]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env final
    weightsOwner weightsPtr weights (positionOffset + position * 768 + index) hWeights (by omega)).append_args
    rfl rfl rfl [.f32 (word weights (token.toNat * 768 + index)), .i32 (PackedGenerateLoop.address outputPtr index)]) ?_
  rintro final values ⟨returned, rfl, rfl, rfl⟩
  wp_packed_frame [hParams, hLength]
  simp only [F32Add.add_eq] at hNext
  apply Frame.of_withValues
    (P := fun result => PackedGenerateLoop.Ready 9 103 104 768 index outputPtr result ∧
      EmbeddingState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) result)
    (R := fun result => wp «module» rest Q final result env)
    (values := [.i64 (Wasm.IEEE32.add (word weights (token.toNat * 768 + index))
      (word weights (positionOffset + position * 768 + index))).toUInt64,
      .i32 (PackedGenerateLoop.address outputPtr index)]) rfl
  · constructor
    · simp only [PackedGenerateLoop.Ready, Locals.get, Locals.validIndex,
        hLength, List.length_set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte, List.getElem?_set,
        Nat.reduceEqDiff, hCounter, hLengthLocal, hPointer,
        show UInt64.ofNat (4 * 768) = 3072 from rfl, true_and]
    · simp (config := { maxDischargeDepth := 64 }) only [EmbeddingState, parameters, hLength,
        List.length_set, List.getElem?_set, Nat.reduceEqDiff, reduceIte, hBytes,
        I64Values.set, hTyped, UInt64.ofNat_uInt32ToNat, and_self]
  · intro result h
    exact hNext result h.1 h.2

#print axioms embeddingWord_spec

end Project.Gpt2CachedStep.CachedHidden
