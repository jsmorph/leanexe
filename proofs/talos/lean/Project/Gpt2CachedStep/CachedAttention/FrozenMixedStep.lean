import Project.Gpt2CachedStep.CachedAttention.FrozenScoresLoop
import Project.Gpt2CachedStep.CachedAttention.FrozenSource
import Project.ProofKit.CheckedNatMulArithmetic
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def mixedBody : Wasm.Program :=
  match (func29[320]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def mixedStep : Wasm.Program :=
  match (mixedBody[33]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

def MixedState (params saved : List Wasm.Value) (probabilityPtr : UInt64)
    (probabilityValues : ByteArray) (position : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 114 ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (position + 1))) ∧
  frame.locals[65]? = some (.i64 probabilityPtr) ∧ frame.locals[66]? = some (.i64 probabilityPtr) ∧
  frame.locals[67]? = some (.i64 (UInt64.ofNat probabilityValues.size)) ∧
  frame.locals[68]? = some (.i64 3072) ∧ I64Values frame.locals ∧ frame.locals.take 68 = saved

def MixedFoldState (params saved : List Wasm.Value) (cache qkv probabilityValues : ByteArray)
    (probabilityPtr outputPtr : UInt64) (layer position index source : Nat) (frame : Locals) : Prop :=
  MixedState params saved probabilityPtr probabilityValues position frame ∧
  frame.locals[69]? = some (.i64 (UInt64.ofNat index)) ∧
  frame.locals[70]? = some (.i64 (UInt64.ofNat (index / 64))) ∧
  frame.locals[72]? = some (.i64 (mixedPrefix cache qkv probabilityValues layer position index source).toUInt64) ∧
  frame.locals[101]? = some (.i64 3072) ∧ frame.locals[102]? = some (.i64 outputPtr) ∧
  frame.locals[105]? = some (.i64 1)

set_option maxRecDepth 32768 in
theorem mixedStep_spec (env : HostEnv Unit) (initial : Store Unit)
    (cacheOwner qkvOwner cachePtr qkvPtr probabilityPtr outputPtr : UInt64)
    (cache qkv probabilityValues : ByteArray) (saved : List Wasm.Value)
    (layer position index source : Nat) (frame : Locals) (values : List Wasm.Value)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hProbabilities : ByteArrayAt initial.mem probabilityPtr.toNat probabilityValues)
    (hLayer : layer < 12) (hPosition : position < 128) (hIndex : index < 768) (hSource : source < position + 1)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hProbabilitySize : 4 * (12 * (position + 1)) ≤ probabilityValues.size)
    (hReady : RangeFoldLoop.Ready 111 112 (position + 1) source frame values)
    (hState : MixedFoldState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
      saved cache qkv probabilityValues probabilityPtr outputPtr layer position index source frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, RangeFoldLoop.Ready 111 112 (position + 1) (source + 1) result values →
      MixedFoldState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
        saved cache qkv probabilityValues probabilityPtr outputPtr layer position index (source + 1) result →
      wp «module» rest Q initial result env) :
    wp «module» (mixedStep ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨hParams, hLength, hSize, hProbabilityOwner, hProbabilityPtr, hProbabilityBytes,
    hBytes, hTyped, hPrefix⟩, hIndexLocal, hHeadLocal, hTotal, hLengthLocal, hPointer, hStride⟩
  simp only [parameters] at hParams
  have hCounter : frame.locals[103]? = some (.i64 (UInt64.ofNat source)) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.1
  have hStop : frame.locals[104]? = some (.i64 (UInt64.ofNat (position + 1))) := by
    simpa [Locals.get, hParams, hLength] using hReady.2.2
  have hHead : index / 64 + 1 ≤ 12 := by omega
  have hLimit := Nat.mul_le_mul_right (position + 1) hHead
  rw [Nat.add_mul, Nat.one_mul] at hLimit
  have hOffset : index / 64 * (position + 1) + source < 12 * (position + 1) := by omega
  have hNonzero : UInt64.ofNat (position + 1) ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' (by change position + 1 < 18446744073709551616; omega)] at this
    change position + 1 = 0 at this
    omega
  have hSafeMul := CheckedNatMul.guard_of_nat_fits (index / 64) (position + 1)
    (by change index / 64 * (position + 1) < 18446744073709551616; omega) hNonzero
  have hMul : UInt64.ofNat (index / 64) * UInt64.ofNat (position + 1) =
      UInt64.ofNat (index / 64 * (position + 1)) := by simp
  have hAdd : UInt64.ofNat (index / 64) * UInt64.ofNat (position + 1) + UInt64.ofNat source =
      UInt64.ofNat (index / 64 * (position + 1) + source) := by simp
  have hSafeAdd : ¬ UInt64.ofNat (index / 64) * UInt64.ofNat (position + 1) + UInt64.ofNat source <
      UInt64.ofNat (index / 64) * UInt64.ofNat (position + 1) := by
    rw [hMul]
    exact CheckedNatAdd.guard_of_fits _ _ (by change index / 64 * (position + 1) + source < 18446744073709551616; omega)
  have hSafeKv : ¬ (768 : UInt64) + UInt64.ofNat index < 768 := by u64_omega
  have hKvIndex : (768 : UInt64) + UInt64.ofNat index = UInt64.ofNat (768 + index) := by simp
  have hSafeInc : ¬ UInt64.ofNat source + 1 < UInt64.ofNat source := by u64_omega
  have hInc : UInt64.ofNat source + 1 = UInt64.ofNat (source + 1) := by simp
  simp only [UInt64.ofNat_add, show UInt64.ofNat 1 = 1 from rfl] at hSafeMul hSafeAdd
  simp only [mixedStep, mixedBody, func29, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.dropLast, List.cons_append, List.nil_append]
  repeat' first
    | wp_packed_frame [hParams, hLength, hTotal, hCounter, hIndexLocal, hHeadLocal, hSize,
        hProbabilityOwner, hProbabilityPtr, hProbabilityBytes, hStop, hStride, hReady.1, hNonzero]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hSafeMul, hSafeAdd])])
  simp only [hAdd]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial
    probabilityPtr probabilityPtr probabilityValues (index / 64 * (position + 1) + source)
    hProbabilities (by omega)).append_args rfl rfl rfl values) ?_
  rintro middle returned ⟨out, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, hLength, hTotal, hCounter, hIndexLocal, hHeadLocal, hSize,
        hStop, hStride, hReady.1]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hSafeKv])])
  simp only [hKvIndex]
  refine wp_call_tw ((CachedKv.cachedKv_exact env middle cacheOwner qkvOwner cachePtr qkvPtr cache qkv
    layer position source (768 + index) hCache hQkv hLayer (by omega) (by omega)
    hCacheSize hQkvSize).append_args rfl rfl rfl values) ?_
  rintro final returned ⟨out, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hParams, hLength, hTotal, hCounter, hIndexLocal, hHeadLocal, hSize,
        hStop, hStride, hReady.1]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hSafeInc])])
  apply hNext
  · simp only [RangeFoldLoop.Ready, Locals.get, hLength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hStop, hInc, true_and]
  · simp (config := { maxDischargeDepth := 64 }) only [MixedFoldState, MixedState, parameters,
      hLength, List.length_set, List.getElem?_set, Nat.reduceLT, Nat.reduceEqDiff, reduceIte,
      hSize, hProbabilityOwner, hProbabilityPtr, hProbabilityBytes, hBytes, hIndexLocal, hHeadLocal,
      hLengthLocal, hPointer, hStride, mixedPrefix_succ, word,
      I64Values.set, hTyped, List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]

#print axioms mixedStep_spec

end Project.Gpt2CachedStep.Frozen.CachedAttention
