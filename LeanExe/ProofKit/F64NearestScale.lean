import LeanExe.ProofKit.F64NearestSteps
import LeanExe.ProofKit.F64NearestSum
import LeanExe.ProofKit.F64PowerScale

/-!
Exact scaling of a nearest word by a power of two, and the absorption of `- 1` by a large word.
`scale_nearest`: if `c` is a nearest word of `s ≥ 2 ^ -1021`, then `c` times the word of
`2 ^ k`, `k ≥ 1`, is `2 ^ k c` exactly and a nearest word of `2 ^ k s`, as long as the product is
finite.  A word below `2 ^ k` times the smallest normal value is farther from `2 ^ k s` than
`2 ^ k c` is, and every other word is `2 ^ k` times a word.  `sub_one_absorbed`: subtracting 1
from a word of value at least `2 ^ 56` gives the word itself.
-/

namespace LeanExe.ProofKit.F64NearestScale
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64NearestSteps

set_option exponentiation.threshold 4096

theorem mul_comm_finite (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.mul a b = Wasm.IEEE64.mul b a := by
  have hs : (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) =
      (Wasm.IEEE64.sign b != Wasm.IEEE64.sign a) := by
    cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;> rfl
  rw [mul_finite_rounder a b ha hb, mul_finite_rounder b a hb ha, Nat.mul_comm, hs]

theorem exponent_lt (v : UInt64) : Wasm.IEEE64.exponent v < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
theorem fraction_lt (v : UInt64) : Wasm.IEEE64.fraction v < 2 ^ 52 := Nat.mod_lt _ (by norm_num)

/-- Word arithmetic in clean contexts, where `omega` stays within its recursion limit. -/
theorem exponent_pos_of (c : UInt64) (h : 2 ^ 52 ≤ c.toNat) (h' : c.toNat < 2 ^ 63) :
    1 ≤ Wasm.IEEE64.exponent c := by
  unfold Wasm.IEEE64.exponent
  omega

theorem nat_sub_one (n k : Nat) (h : k + 1 ≤ n) : k ≤ n - 1 := by omega

theorem nat_pred_bounds (n L : Nat) (hn : n < L) (hL : L < 2 ^ 63) (h1 : 1 ≤ n) :
    n - 1 < L ∧ n - 1 + 1 < 2 ^ 63 ∧ n - 1 + 1 = n := by omega

theorem nat_succ_bounds (n m L : Nat) (hnm : n < m) (hm : m < L) (hL : L < 2 ^ 63) :
    n + 1 < L ∧ n + 1 < 2 ^ 63 ∧ n + 1 ≤ m := by omega

/-- A nonnegative word below the limit has exponent field below 2047. -/
theorem exponent_of_lt_limit (v : UInt64) (hv : v.toNat < limit) :
    Wasm.IEEE64.exponent v < 2047 := by
  have hl : limit = 2047 * 2 ^ 52 := rfl
  unfold Wasm.IEEE64.exponent
  rw [hl] at hv
  omega

/-- The value of a nonnegative word with exponent field `e ≥ 1`. -/
theorem normal_value' (v : UInt64) (hv : v.toNat < limit) (he : 1 ≤ Wasm.IEEE64.exponent v) :
    value v = ((2 ^ 52 + Wasm.IEEE64.fraction v : Nat) * 2 ^ (Wasm.IEEE64.exponent v - 1) : Nat) /
      (2 : ℝ) ^ 1074 := by
  rw [F64NearestSum.value_of_lt_limit v hv]
  congr 2
  unfold Wasm.IEEE64.scaledMagnitude
  simp [show Wasm.IEEE64.exponent v ≠ 0 by omega]

theorem scale_nearest (s : ℝ) (c : UInt64) (k : Nat) (hk : 1 ≤ k) (hk' : k ≤ 1023) (hc : Nearest s c)
    (hs : 1 / (2 : ℝ) ^ 1021 ≤ s) (hfin : Wasm.IEEE64.exponent c + k < 2047) :
    Finite (Wasm.IEEE64.mul c (Wasm.IEEE64.encodeFinite false (1023 + k) 0)) ∧
      value (Wasm.IEEE64.mul c (Wasm.IEEE64.encodeFinite false (1023 + k) 0)) =
        (2 : ℝ) ^ k * value c ∧
      Nearest ((2 : ℝ) ^ k * s) (Wasm.IEEE64.mul c (Wasm.IEEE64.encodeFinite false (1023 + k) 0)) := by
  have hcl := hc.1
  have hcf : Finite c := (F64NearestNonnegative.nearest_finite s c hc).1
  have hcs : Wasm.IEEE64.sign c = false := (F64NearestNonnegative.nearest_finite s c hc).2
  -- `c` is normal: it lies at or above the smallest normal word.
  have hmn0 : 1 * 2 ^ 52 < limit :=
    lt_of_le_of_lt (Nat.le_add_right _ _) (boundary_lt_limit 1 (by norm_num))
  have hmnw : (UInt64.ofNat (1 * 2 ^ 52)).toNat = 1 * 2 ^ 52 := word_toNat _ hmn0
  have hmn : (UInt64.ofNat (1 * 2 ^ 52)).toNat < limit := by rw [hmnw]; exact hmn0
  have hmv : value (UInt64.ofNat (1 * 2 ^ 52)) = 1 / (2 : ℝ) ^ 1022 := by
    rw [F64PositiveSpacing.boundary_value 1 le_rfl (by norm_num)]
    norm_num
  have h21 : (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 1021 := by norm_num
  have hcn := nearest_ge s c _ hc hmn (by rw [hmv]; linarith)
  rw [hmnw] at hcn
  have hce : 1 ≤ Wasm.IEEE64.exponent c :=
    exponent_pos_of c (by simpa using hcn) (hcl.trans limit_lt)
  have hpf : Finite (Wasm.IEEE64.encodeFinite false (1023 + k) 0) :=
    finite_encodeFinite false _ 0 (by omega) (by norm_num)
  rw [mul_comm_finite c _ hcf hpf]
  have hm := F64PowerScale.mul_power_finite (1023 + k) c (by omega) (by omega) hcf hce (by omega)
    (by omega)
  have hpow : (2 : ℝ) ^ (((1023 + k : Nat) : Int) - 1023) = 2 ^ k := by
    rw [show ((1023 + k : Nat) : Int) - 1023 = (k : Int) by push_cast; ring, zpow_natCast]
  rw [hpow] at hm
  refine ⟨hm.1, hm.2, ?_⟩
  have hword := F64PowerScale.mul_power (1023 + k) c (by omega) (by omega) hcf hce (by omega)
  rw [ite_eq_right (by omega), hcs] at hword
  constructor
  · rw [hword]
    have hlt : (Wasm.IEEE64.encodeFinite false (Wasm.IEEE64.exponent c + (1023 + k) - 1023)
        (Wasm.IEEE64.fraction c)).toNat < limit := by
      apply F64Magnitude.lt_limit_of_finite
      · exact finite_encodeFinite _ _ _ (by omega) (fraction_lt c)
      · exact sign_encodeFinite _ _ _ (by omega) (fraction_lt c)
    exact hlt
  · intro v hv
    rw [hm.2]
    have hvs : Wasm.IEEE64.sign v = false := by
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
      exact hv.trans limit_lt
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    rcases Nat.lt_or_ge (Wasm.IEEE64.exponent v) (k + 1) with hve | hve
    · -- `v` lies below `2 ^ k` times the smallest normal value.
      have hvsmall : value v < (2 : ℝ) ^ k / 2 ^ 1022 := by
        rw [F64NearestSum.value_of_lt_limit v hv]
        have hm : Wasm.IEEE64.scaledMagnitude v < 2 ^ 52 * 2 ^ k := by
          unfold Wasm.IEEE64.scaledMagnitude
          have hf := fraction_lt v
          by_cases h0 : Wasm.IEEE64.exponent v = 0
          · simp only [h0, beq_self_eq_true, ite_true]
            have : 2 ^ 52 * 1 ≤ 2 ^ 52 * 2 ^ k := Nat.mul_le_mul_left _ Nat.one_le_two_pow
            omega
          · have hb : (Wasm.IEEE64.exponent v == 0) = false := by simpa using h0
            simp only [hb, Bool.false_eq_true, ite_false]
            calc (2 ^ 52 + Wasm.IEEE64.fraction v) * 2 ^ (Wasm.IEEE64.exponent v - 1) <
                2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent v - 1) :=
                  Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
              _ ≤ 2 ^ 52 * 2 ^ k := by
                rw [← pow_add, ← pow_add]
                exact Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        have : (Wasm.IEEE64.scaledMagnitude v : ℝ) < 2 ^ 52 * 2 ^ k := by exact_mod_cast hm
        calc (Wasm.IEEE64.scaledMagnitude v : ℝ) * 2 ^ 1022 < 2 ^ 52 * 2 ^ k * 2 ^ 1022 := by
              gcongr
          _ = 2 ^ k * 2 ^ 1074 := by ring
      have hcmn := hc.2 _ hmn
      rw [hmv] at hcmn
      have hsmn : 1 / (2 : ℝ) ^ 1022 ≤ s := le_trans h21 hs
      rw [abs_of_nonpos (by linarith : 1 / (2 : ℝ) ^ 1022 - s ≤ 0)] at hcmn
      calc |2 ^ k * value c - 2 ^ k * s| = 2 ^ k * |value c - s| := by
            rw [← mul_sub, abs_mul, abs_of_pos h2k]
        _ ≤ 2 ^ k * (s - 1 / 2 ^ 1022) := by gcongr; linarith
        _ = 2 ^ k * s - 2 ^ k / 2 ^ 1022 := by ring
        _ ≤ 2 ^ k * s - value v := by linarith
        _ ≤ |value v - 2 ^ k * s| := by rw [abs_sub_comm]; exact le_abs_self _
    · -- `v` is `2 ^ k` times a word.
      set v' := Wasm.IEEE64.encodeFinite false (Wasm.IEEE64.exponent v - k)
        (Wasm.IEEE64.fraction v)
      have hve' : Wasm.IEEE64.exponent v < 2047 := exponent_of_lt_limit v hv
      have hv'l : v'.toNat < limit := by
        apply F64Magnitude.lt_limit_of_finite
        · exact finite_encodeFinite _ _ _ (by omega) (fraction_lt v)
        · exact sign_encodeFinite _ _ _ (by omega) (fraction_lt v)
      have hv'e : Wasm.IEEE64.exponent v' = Wasm.IEEE64.exponent v - k :=
        exponent_encodeFinite _ _ _ (by omega) (fraction_lt v)
      have hv'f : Wasm.IEEE64.fraction v' = Wasm.IEEE64.fraction v :=
        fraction_encodeFinite _ _ _ (by omega) (fraction_lt v)
      have hvv : value v = 2 ^ k * value v' := by
        rw [normal_value' v hv (by omega), normal_value' v' hv'l (by rw [hv'e]; omega), hv'e,
          hv'f]
        push_cast
        rw [show Wasm.IEEE64.exponent v - 1 = k + (Wasm.IEEE64.exponent v - k - 1) by omega,
          pow_add]
        ring
      have h := hc.2 v' hv'l
      rw [hvv, ← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_pos h2k]
      exact mul_le_mul_of_nonneg_left h h2k.le

/-- Subtracting 1 from a word of value at least `2 ^ 56` and below `2 ^ 1023` gives the word. -/
theorem sub_one_absorbed (v : UInt64) (hvf : Finite v) (hv : (2 : ℝ) ^ 56 ≤ value v)
    (hv' : value v < (2 : ℝ) ^ 1023) :
    Wasm.IEEE64.sub v 0x3FF0000000000000 = v := by
  have h1f : Finite (0x3FF0000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  have h1v : value (0x3FF0000000000000 : UInt64) = 1 := by
    have h : Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) = 2 ^ 1074 := by
      decide +kernel
    rw [value, h]; norm_num
  have hn := F64NearestSum.sub_nearest v _ hvf h1f (by rw [h1v]; linarith)
    (by rw [h1v]; linarith)
  rw [h1v] at hn
  set c := Wasm.IEEE64.sub v 0x3FF0000000000000
  have hl63 := limit_lt
  have hvp : 0 < value v := lt_of_lt_of_le (by positivity) hv
  have hvl : v.toNat < limit := positive_finite_encoding v hvf hvp
  have hcv := hn.2 v hvl
  rw [show value v - (value v - 1) = 1 by ring, abs_one] at hcv
  have hcd := abs_le.mp hcv
  have hcl := hn.1
  have hB0 : 1079 * 2 ^ 52 < limit := by unfold limit; norm_num
  have hB : (UInt64.ofNat (1079 * 2 ^ 52)).toNat = 1079 * 2 ^ 52 := word_toNat _ hB0
  have hbv : value (UInt64.ofNat (1079 * 2 ^ 52)) = (2 : ℝ) ^ 56 := by
    rw [F64PositiveSpacing.boundary_value 1079 (by norm_num) (by norm_num)]; norm_num
  have hve : 1079 * 2 ^ 52 ≤ v.toNat := by
    have := (value_le_iff (by rw [hB]; exact hB0.trans hl63) (hvl.trans hl63)).mp
      (by rw [hbv]; exact hv)
    rwa [hB] at this
  have hv1 : 1078 * 2 ^ 52 ≤ v.toNat - 1 := nat_sub_one _ _ (le_trans (by norm_num) hve)
  have hv0 : 1 ≤ v.toNat := le_trans (by norm_num) hve
  apply UInt64.toNat_inj.mp
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨hpl, hp63, hpeq⟩ := nat_pred_bounds _ _ hvl hl63 hv0
    have hP : (UInt64.ofNat (v.toNat - 1)).toNat = v.toNat - 1 := word_toNat _ hpl
    have hg := F64FullStep.gap_lower (v.toNat - 1) 1078 hv1 hp63
    rw [hpeq, UInt64.ofNat_toNat] at hg
    have hle := (value_le_iff (hcl.trans hl63) (by rw [hP]; exact hpl.trans hl63)).mpr
      (by rw [hP]; exact Nat.le_sub_one_of_lt hlt)
    have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (1078 - 1) / 2 ^ 1074 := by norm_num
    linarith
  · obtain ⟨hsl, hs63, hsle⟩ := nat_succ_bounds _ _ _ hgt hcl hl63
    have hS : (UInt64.ofNat (v.toNat + 1)).toNat = v.toNat + 1 := word_toNat _ hsl
    have hg := F64FullStep.gap_lower v.toNat 1079 hve hs63
    rw [UInt64.ofNat_toNat] at hg
    have hle := (value_le_iff (by rw [hS]; exact hs63) (hcl.trans hl63)).mpr
      (by rw [hS]; exact hsle)
    have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (1079 - 1) / 2 ^ 1074 := by norm_num
    linarith

#print axioms mul_comm_finite
#print axioms scale_nearest
#print axioms sub_one_absorbed

end LeanExe.ProofKit.F64NearestScale
