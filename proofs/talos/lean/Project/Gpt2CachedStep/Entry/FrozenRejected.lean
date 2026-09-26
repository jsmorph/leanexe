import Project.Gpt2CachedStep.Entry.FrozenGuardValid

namespace Project.Gpt2CachedStep.Frozen.Entry
open Wasm Project.Common Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2

theorem cachedStep_invalid {weights cache : ByteArray} {token : UInt32} {position : Nat}
    (h : ¬Valid weights cache token position) :
    cachedStep weights cache token position = { cache := ByteArray.empty, logits := ByteArray.empty } := by
  unfold cachedStep
  split
  · rfl
  · rename_i hGuard
    exfalso
    apply h
    simpa [Valid, vocabulary, cachePositionWords, Nat.mul_assoc, and_assoc] using hGuard

theorem cachedStep_rejected (env : HostEnv Unit) (initial : Store Unit)
    (weightsPtr cachePtr : UInt64) (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (hWeightsFit : weights.size < UInt64.size) (hCacheFit : cache.size < UInt64.size)
    (hPositionFit : position < UInt64.size) (hInvalid : ¬Valid weights cache token position) :
    TerminatesWith env «module» 38 initial
      [.i64 (UInt64.ofNat position), .i64 token.toUInt64, .i64 (UInt64.ofNat cache.size), .i64 cachePtr,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr]
      (fun final values => final = initial ∧ values = [.i64 0, .i64 0, .i64 0, .i64 0]) := by
  have hWeightsWord : UInt64.ofNat weights.size = 497759232 ↔ weights.size = parameterWords * 4 := by
    constructor
    · exact Project.Common.ofNat_inj hWeightsFit (by decide)
    · intro h
      rw [h]
      rfl
  have hTokenWord : (50257 : UInt64) ≤ token.toUInt64 ↔ 50257 ≤ token.toNat := by
    simp only [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]
    rfl
  have hPositionWord : (128 : UInt64) ≤ UInt64.ofNat position ↔ 128 ≤ position := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hPositionFit]
    rfl
  have hCases :
      (weights.size ≠ parameterWords * 4) ∨
      (weights.size = parameterWords * 4 ∧ 50257 ≤ token.toNat) ∨
      (weights.size = parameterWords * 4 ∧ token.toNat < 50257 ∧ 128 ≤ position) ∨
      (weights.size = parameterWords * 4 ∧ token.toNat < 50257 ∧ position < 128 ∧ cache.size ≠ position * 73728) := by
    unfold Valid at hInvalid
    omega
  rcases hCases with hw | ⟨hw, ht⟩ | ⟨hw, ht, hp⟩ | ⟨hw, ht, hp, hc⟩
  all_goals
    try have hSmallToken : ¬50257 ≤ token.toNat := by omega
    try have hSmallPosition : ¬128 ≤ position := by omega
    refine TerminatesWith.of_wp_entry_for (f := func38Def) rfl ?_
    change wp «module» func38 _ initial
      { params := parameters weightsPtr cachePtr weights cache token position, locals := List.replicate 55 (.i64 0) } env
    rw [emitted_guard]
    simp only [func38, List.take, List.cons_append, List.nil_append]
    wp_packed_frame [parameters, List.getElem?_cons_zero, List.getElem?_cons_succ]
    refine wp_call_tw ((Layout.parameterWords_exact env initial).append_args rfl rfl rfl
      [.i64 (UInt64.ofNat weights.size)]) ?_
    rintro final values ⟨_, rfl, rfl, rfl⟩
    repeat' first
      | wp_packed_frame [*, parameters, rejectedBody, returnCode, func38Def, Function.numParams,
          List.getElem?_cons_zero, List.getElem?_cons_succ,
          show UInt64.ofNat parameterWords = 124439808 from rfl,
          show (124439808 : UInt64) * 4 = 497759232 from rfl]
      | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
      | exact And.intro True.intro True.intro
  have hCacheWord : UInt64.ofNat cache.size ≠ UInt64.ofNat position * 18432 * 4 := by
    change UInt64.ofNat cache.size ≠ UInt64.ofNat position * UInt64.ofNat 18432 * UInt64.ofNat 4
    rw [← UInt64.ofNat_mul, ← UInt64.ofNat_mul]
    intro h
    have hFit : position * 18432 * 4 < UInt64.size := by change position * 18432 * 4 < 18446744073709551616; omega
    have := Project.Common.ofNat_inj hCacheFit hFit h
    omega
  have hMulPosition : ¬(-1 : UInt64) / 18432 < UInt64.ofNat position := by
    change ¬(1000799917193443 : UInt64) < UInt64.ofNat position
    u64_omega
  have hMulCache : ¬(-1 : UInt64) / 4 < UInt64.ofNat position * 18432 := by
    simpa only [UInt64.ofNat_mul, show UInt64.ofNat 18432 = 18432 from rfl,
      show UInt64.ofNat 4 = 4 from rfl] using CheckedNatMul.guard_of_nat_fits (position * 18432) 4
        (by change position * 18432 * 4 < 18446744073709551616; omega) (by decide)
  refine wp_call_tw ((Layout.cachePositionWords_exact env final).append_args rfl rfl rfl
    [.i64 (UInt64.ofNat cache.size)]) ?_
  rintro final values ⟨_, rfl, rfl, rfl⟩
  repeat' first
    | wp_packed_frame [*, parameters, rejectedBody, returnCode, func38Def, Function.numParams,
        List.getElem?_cons_zero, List.getElem?_cons_succ,
        show UInt64.ofNat cachePositionWords = 18432 from rfl]
    | (refine wp_iff_cons rfl ?_; first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])
    | exact And.intro True.intro True.intro

#print axioms cachedStep_rejected

end Project.Gpt2CachedStep.Frozen.Entry
