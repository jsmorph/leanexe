import Project.Gpt2CachedStep.LayerNorm.MeansLoop
import Project.Gpt2RowInvStd.Source

namespace Project.Gpt2CachedStep.LayerNorm
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2
open Project.Gpt2RowInvStd (variancePrefix variancePrefix_succ rowInvStd_eq)

def inversesBody : Wasm.Program :=
  match (func20[91]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def varianceStep : Wasm.Program :=
  match (inversesBody[26]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

def InversesState (params : List Wasm.Value) (meansOwner meansPtr : UInt64) (rows : Nat)
    (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 74 ∧
  frame.locals[7]? = some (.i64 meansOwner) ∧
  frame.locals[8]? = some (.i64 meansPtr) ∧
  frame.locals[9]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧
  frame.locals[10]? = some (.i64 (UInt64.ofNat (4 * rows)))

def VarianceState (params : List Wasm.Value) (input : ByteArray)
    (meansOwner meansPtr outputPtr : UInt64) (rows row index : Nat) (frame : Locals) : Prop :=
  InversesState params meansOwner meansPtr rows frame ∧
  frame.locals[11]? = some (.i64 (UInt64.ofNat row)) ∧
  frame.locals[13]? = some (.i64 (variancePrefix input row (word (means input rows) row) index).toUInt64) ∧
  frame.locals[61]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧
  frame.locals[62]? = some (.i64 outputPtr) ∧
  frame.locals[65]? = some (.i64 1)

set_option maxRecDepth 32768 in
theorem varianceStep_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner inputOwner weightsPtr inputPtr meansOwner meansPtr outputPtr : UInt64)
    (weights input : ByteArray) (scaleOffset biasOffset rows row index : Nat)
    (frame : Locals) (values : List Wasm.Value)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hMeans : ByteArrayAt initial.mem meansPtr.toNat (means input rows))
    (hRow : (row + 1) * 768 * 4 ≤ input.size) (hRows : row < rows) (hIndex : index < 768)
    (hReady : RangeFoldLoop.Ready 72 73 768 index frame values)
    (hState : VarianceState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) input meansOwner meansPtr outputPtr rows row index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, RangeFoldLoop.Ready 72 73 768 (index + 1) result values →
      VarianceState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
        scaleOffset biasOffset rows) input meansOwner meansPtr outputPtr rows row (index + 1) result →
      wp «module» rest Q initial result env) :
    wp «module» (varianceStep ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨hParams, hLength, hMeansOwner, hMeansPtr, hMeansSize, hBytes⟩,
    hRowLocal, hTotal, hLengthLocal, hPointer, hStride⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[63]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hStop : frame.locals[64]? = some (.i64 768) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2
  have hRow64 : row < UInt64.size := by
    have := hInput.1
    change row < 18446744073709551616
    omega
  have hBase64 : row * 768 < UInt64.size := by
    have := hInput.1
    change row * 768 < 18446744073709551616
    omega
  have hOffset64 : row * 768 + index < UInt64.size := by
    have := hInput.1
    change row * 768 + index < 18446744073709551616
    omega
  have hSafe : ¬ (-1 : UInt64) / 768 < UInt64.ofNat row := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hRow64]
    change ¬ 24019198012642645 < row
    have := hInput.1
    omega
  have hMul : UInt64.ofNat row * 768 = UInt64.ofNat (row * 768) := by simp
  have hAdd : UInt64.ofNat row * 768 + UInt64.ofNat index =
      UInt64.ofNat (row * 768 + index) := by simp
  have hSafeAdd : ¬ UInt64.ofNat row * 768 + UInt64.ofNat index < UInt64.ofNat row * 768 := by
    rw [hAdd, hMul, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' hOffset64, UInt64.toNat_ofNat_of_lt' hBase64]
    omega
  have hInc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
  have hSafeInc : ¬ UInt64.ofNat index + 1 < UInt64.ofNat index := by
    rw [hInc, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' (by change index + 1 < 18446744073709551616; omega),
      UInt64.toNat_ofNat_of_lt' (by change index < 18446744073709551616; omega)]
    omega
  simp only [varianceStep, inversesBody, func20, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.dropLast, List.cons_append, List.nil_append]
  repeat' first
    | wp_packed_frame [hParams, hLength, hTotal, hCounter, hRowLocal, hStop, hStride, hReady.1]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hSafe, hSafeAdd])])
  simp only [hAdd]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env initial inputOwner inputPtr input (row * 768 + index) hInput (by omega)).append_args
    rfl rfl rfl values) ?_
  rintro middle returned ⟨out, rfl, rfl, rfl⟩
  wp_packed_frame [hParams, hLength, hTotal, hCounter, hRowLocal, hMeansOwner, hMeansPtr,
    hMeansSize, hStop, hStride, hReady.1]
  have hMeanRead := PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env middle meansOwner meansPtr (means input rows) row hMeans (by rw [means_size]; omega)
  rw [means_size] at hMeanRead
  refine wp_call_tw (hMeanRead.append_args rfl rfl rfl
    (.f32 (word input (row * 768 + index)) :: values)) ?_
  rintro final returned ⟨out, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, hLength, hTotal, hCounter, hRowLocal, hStop, hStride, hReady.1]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hSafeInc])])
  apply hNext
  · simp only [RangeFoldLoop.Ready, Locals.get, hLength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hStop, hInc, true_and]
    rfl
  · simp only [VarianceState, InversesState, parameters, hLength, List.length_set, List.getElem?_set,
      Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hMeansOwner, hMeansPtr, hMeansSize, hBytes,
      hRowLocal, hLengthLocal, hPointer, hStride, variancePrefix_succ, word, and_self]

#print axioms varianceStep_spec

end Project.Gpt2CachedStep.LayerNorm
