import Project.Gpt2QuantizedCached.Entry.Header
import Project.ProofKit.CheckedNatMul
import Project.Common

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Common Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def inputTestCode : Program :=
  [.constI64 50257,
   .localGet 6,
   .leUI64,
   .iff 0 1 [
    .const 1
   ] [
    .constI64 128,
    .localGet 7,
    .leUI64
   ] [] [.i32],
   .iff 0 1 [
    .const 1
   ] [
    .localGet 5,
    .localGet 7,
    .localSet 98,
    .call 29,
    .localSet 99,
    .localGet 99,
    .constI64 0,
    .eqI64,
    .iff 0 1 [
     .constI64 0
    ] [
     .constI64 (-1),
     .localGet 99,
     .divUI64,
     .localGet 98,
     .ltUI64,
     .iff 0 1 [
      .unreachable
     ] [
      .localGet 98,
      .localGet 99,
      .mulI64
     ] [] [.i64]
    ] [] [.i64],
    .localSet 96,
    .constI64 4,
    .localSet 97,
    .localGet 97,
    .constI64 0,
    .eqI64,
    .iff 0 1 [
     .constI64 0
    ] [
     .constI64 (-1),
     .localGet 97,
     .divUI64,
     .localGet 96,
     .ltUI64,
     .iff 0 1 [
      .unreachable
     ] [
      .localGet 96,
      .localGet 97,
      .mulI64
     ] [] [.i64]
    ] [] [.i64],
    .eqI64,
    .iff 0 1 [
     .constI64 1
    ] [
     .constI64 0
    ] [] [.i64],
    .constI64 0,
    .eqI64,
    .eqz,
    .eqz
   ] [] [.i32]]

theorem emitted_inputTest : inputBody.take 12 = inputTestCode ++ ReadOnlyDisjunction.canonicalProgram := rfl

theorem inputTest_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hCacheFit : cache.size < UInt64.size) (hPositionFit : position < UInt64.size)
    (hState : State (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = frame.params → result.locals.length = 93 →
      I64Values result.locals → result.values = [.i32 (if invalidInput cache token position then 1 else 0)] →
      wp «module» rest Q initial result env) :
    wp «module» (inputTestCode ++ rest) Q initial frame env := by
  have hTokenWord : (50257 : UInt64) ≤ token.toUInt64 ↔ 50257 ≤ token.toNat := by
    simp only [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]
    rfl
  have hPositionWord : (128 : UInt64) ≤ UInt64.ofNat position ↔ 128 ≤ position := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hPositionFit]
    rfl
  by_cases ht : 50257 ≤ token.toNat
  · simp only [inputTestCode, List.cons_append, List.nil_append]
    wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hState.values,
      List.getElem?_cons_zero, List.getElem?_cons_succ]
    simp only [wp_iff_control_types, hTokenWord, ht, ite_true]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_packed_frame []
    try simp only [wp_iff_control_types]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_packed_frame []
    apply hNext
    · exact hState.paramsEq.symm
    · exact hState.length
    · exact hState.typed
    · simp [invalidInput, ht]
  · by_cases hp : 128 ≤ position
    · simp only [inputTestCode, List.cons_append, List.nil_append]
      wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hState.values,
        List.getElem?_cons_zero, List.getElem?_cons_succ]
      simp only [hTokenWord, ht, ite_false]
      refine wp_iff_cons rfl ?_
      rw [ite_eq_right (by decide)]
      wp_packed_frame [List.getElem?_cons_zero, List.getElem?_cons_succ]
      simp only [hPositionWord, hp, ite_true]
      refine wp_iff_cons rfl ?_
      rw [ite_eq_left (by decide)]
      wp_packed_frame []
      apply hNext
      · exact hState.paramsEq.symm
      · exact hState.length
      · exact hState.typed
      · simp [invalidInput, ht, hp]
    · have hPosition : position < 128 := by omega
      have hCacheWord : UInt64.ofNat cache.size = UInt64.ofNat position * 18432 * 4 ↔
          cache.size = position * 73728 := by
        change UInt64.ofNat cache.size = UInt64.ofNat position * UInt64.ofNat 18432 * UInt64.ofNat 4 ↔ _
        rw [← UInt64.ofNat_mul, ← UInt64.ofNat_mul]
        have hFit : position * 18432 * 4 < UInt64.size := by change position * 18432 * 4 < 18446744073709551616; omega
        constructor
        · intro h
          have := Project.Common.ofNat_inj hCacheFit hFit h
          omega
        · intro h
          congr 1
          omega
      have hMulPosition : ¬(-1 : UInt64) / 18432 < UInt64.ofNat position := by
        change ¬(1000799917193443 : UInt64) < UInt64.ofNat position
        u64_omega
      have hMulCache : ¬(-1 : UInt64) / 4 < UInt64.ofNat position * 18432 := by
        simpa only [UInt64.ofNat_mul, show UInt64.ofNat 18432 = 18432 from rfl,
          show UInt64.ofNat 4 = 4 from rfl] using CheckedNatMul.guard_of_nat_fits (position * 18432) 4
            (by change position * 18432 * 4 < 18446744073709551616; omega) (by decide)
      simp only [inputTestCode, List.cons_append, List.nil_append]
      wp_packed_frame [hState.paramsEq, parameters, CachedHidden.parameters, hState.length, hState.values,
        List.getElem?_cons_zero, List.getElem?_cons_succ]
      simp only [hTokenWord, ht, ite_false]
      refine wp_iff_cons rfl ?_
      rw [ite_eq_right (by decide)]
      wp_packed_frame [List.getElem?_cons_zero, List.getElem?_cons_succ]
      simp only [hPositionWord, hp, ite_false]
      refine wp_iff_cons rfl ?_
      rw [ite_eq_right (by decide)]
      wp_packed_frame [hState.length, List.getElem?_cons_zero, List.getElem?_cons_succ]
      refine wp_call_tw ((Layout.cachePositionWords_exact env initial).append_args rfl rfl rfl
        [.i64 (UInt64.ofNat cache.size)]) ?_
      rintro final returned ⟨_, rfl, hFinal, rfl⟩
      subst final
      by_cases hcw : UInt64.ofNat cache.size = UInt64.ofNat position * 18432 * 4
      all_goals
        wp_packed_frame [hState.length, show UInt64.ofNat cachePositionWords = 18432 from rfl]
        refine wp_iff_cons rfl ?_
        rw [ite_eq_right (by decide)]
        wp_packed_frame [hState.length]
        simp only [hMulPosition, ite_false]
        refine wp_iff_cons rfl ?_
        rw [ite_eq_right (by decide)]
        wp_packed_frame [hState.length]
        refine wp_iff_cons rfl ?_
        rw [ite_eq_right (by decide)]
        wp_packed_frame [hState.length]
        simp only [hMulCache, ite_false]
        refine wp_iff_cons rfl ?_
        rw [ite_eq_right (by decide)]
        wp_packed_frame [hState.length]
        simp only [hcw, ite_true, ite_false]
        refine wp_iff_cons rfl ?_
        first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
        wp_packed_frame []
        apply hNext
        · simpa only [parameters, CachedHidden.parameters, hcw] using hState.paramsEq.symm
        · simpa only [List.length_set] using hState.length
        · simp (config := { maxDischargeDepth := 32 }) only [I64Values.set, hState.typed]
        · simp only [hCacheWord] at hcw
          simp [invalidInput, ht, hp, cachePositionWords, Nat.mul_assoc, hcw]

#print axioms inputTest_spec
end Project.Gpt2QuantizedCached.Entry
