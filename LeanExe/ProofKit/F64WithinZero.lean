import LeanExe.ProofKit.F64RoundNearest

/-!
A word closer to `y` than half the spacing on either side of it is the nearest-even reference of
`y`: every other word lies at least one spacing away from it.  `within_zero_of_close` states this
as `WithinSteps 0` for a word whose two neighbours lie in its binade.
-/

namespace LeanExe.ProofKit.F64WithinZero
open CodeLib.IEEE64 F64NearestNonnegative F64RoundNearest

set_option exponentiation.threshold 4096

/-- A positive word in binade `n`, not at its start, within half a spacing of `y`, is the
nonnegative reference of `y`. -/
theorem reference_of_close (y : ℝ) (c : UInt64) (n : ℕ) (hn1 : 1 ≤ n)
    (hcn : n * 2 ^ 52 + 1 ≤ c.toNat) (hcl : c.toNat + 2 < limit)
    (h : |value c - y| < (2 : ℝ) ^ (n - 1) / 2 ^ 1074 / 2) (hyt : y < 2 ^ 1023) :
    F64PositiveRounding.roundNearestEven y = c := by
  have hlim : limit = 2047 * 2 ^ 52 := rfl
  have hcl' : c.toNat < limit := by omega
  have word (m : ℕ) (hm : m < 2 ^ 63) : (UInt64.ofNat m).toNat = m :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hh : (0 : ℝ) < (2 : ℝ) ^ (n - 1) / 2 ^ 1074 := by positivity
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  -- every other word is at least one spacing away
  have hfar : ∀ v : UInt64, v.toNat < limit → v ≠ c →
      (2 : ℝ) ^ (n - 1) / 2 ^ 1074 ≤ |value v - value c| := by
    intro v hv hvc
    have hne : v.toNat ≠ c.toNat := fun he => hvc (UInt64.toNat_inj.mp he)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hc63 : c.toNat - 1 + 1 < 2 ^ 63 := by rw [hlim] at hcl'; omega
      have g := F64FullStep.gap_lower (c.toNat - 1) n (Nat.le_sub_one_of_lt hcn) hc63
      rw [show c.toNat - 1 + 1 = c.toNat by omega, UInt64.ofNat_toNat] at g
      have hw1 : (UInt64.ofNat (c.toNat - 1)).toNat = c.toNat - 1 := word _ (by omega)
      have hv63 : v.toNat < 2 ^ 63 := by rw [hlim] at hv; omega
      have hle : value v ≤ value (UInt64.ofNat (c.toNat - 1)) :=
        (F64PositiveOrder.value_le_iff hv63 (by rw [hw1]; omega)).mpr (by rw [hw1]; omega)
      rw [abs_of_neg (by linarith)]
      linarith
    · have hc63 : c.toNat + 1 < 2 ^ 63 := by rw [hlim] at hcl'; omega
      have g := F64FullStep.gap_lower c.toNat n (Nat.le_of_succ_le hcn) hc63
      rw [UInt64.ofNat_toNat] at g
      have hw1 : (UInt64.ofNat (c.toNat + 1)).toNat = c.toNat + 1 := word _ hc63
      have hv63 : v.toNat < 2 ^ 63 := by rw [hlim] at hv; omega
      have hle : value (UInt64.ofNat (c.toNat + 1)) ≤ value v :=
        (F64PositiveOrder.value_le_iff (by rw [hw1]; exact hc63) hv63).mpr (by rw [hw1]; omega)
      rw [abs_of_pos (by linarith)]
      linarith
  have hN : Nearest y c := by
    refine ⟨hcl', fun v hv => ?_⟩
    by_cases hvc : v = c
    · rw [hvc]
    · have := hfar v hv hvc
      have h3 := abs_sub_le (value v) y (value c)
      rw [abs_sub_comm y (value c)] at h3
      linarith [abs_lt.mpr ⟨h1, h2⟩]
  have hNE : NearestEven y c := by
    refine ⟨hN, fun v hv => ?_⟩
    by_cases hvc : v = c
    · rw [hvc]
    · exfalso
      have := hfar v hv.1 hvc
      have h4 := hv.2 c hcl'
      have h3 := abs_sub_le (value v) y (value c)
      rw [abs_sub_comm y (value c)] at h3
      linarith [abs_lt.mpr ⟨h1, h2⟩]
  have hyo : y < F64PositiveRounding.overflowThreshold := by
    have : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 := rfl
    rw [this]
    have : (2 : ℝ) ^ 1023 ≤ 2 ^ 1024 - 2 ^ 970 := by norm_num
    linarith
  rw [F64PositiveRounding.reference_finite y hyo]
  exact F64NearestEven.roundNearestEven_eq y c hNE

theorem within_zero_pos (y : ℝ) (c : UInt64) (n : ℕ) (hn1 : 1 ≤ n) (hpos : c.toNat < 2 ^ 63)
    (hcn : n * 2 ^ 52 + 1 ≤ c.toNat) (hcl : c.toNat + 2 < limit)
    (h : |value c - y| < (2 : ℝ) ^ (n - 1) / 2 ^ 1074 / 2) (hyt : |y| < 2 ^ 1023) :
    F64SignedRounding.WithinSteps 0 y c := by
  have hlim : limit = 2047 * 2 ^ 52 := rfl
  have hB := F64PositiveSpacing.boundary_value n hn1 (by rw [hlim] at hcl; omega)
  have hcv : value (UInt64.ofNat (n * 2 ^ 52)) ≤ value c := by
    have hw : (UInt64.ofNat (n * 2 ^ 52)).toNat = n * 2 ^ 52 :=
      UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
    exact (F64PositiveOrder.value_le_iff (by rw [hw]; omega) hpos).mpr
      (by rw [hw]; exact Nat.le_of_succ_le hcn)
  have hy0 : 0 ≤ y := by
    have h1 := (abs_lt.mp h).2
    have h2 : (2 : ℝ) ^ (n - 1) / 2 ^ 1074 / 2 < value (UInt64.ofNat (n * 2 ^ 52)) := by
      rw [hB]
      have : (2 : ℝ) ^ (n - 1) ≤ 2 ^ (n + 51) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hp : (0 : ℝ) < (2 : ℝ) ^ (n - 1) / 2 ^ 1074 := by positivity
      have h3 : (2 : ℝ) ^ (n - 1) / 2 ^ 1074 / 2 < 2 ^ (n - 1) / 2 ^ 1074 := by linarith
      exact h3.trans_le (div_le_div_of_nonneg_right this (by positivity))
    set B := value (UInt64.ofNat (n * 2 ^ 52))
    set hh := (2 : ℝ) ^ (n - 1) / 2 ^ 1074 / 2
    linarith
  have hr := reference_of_close y c n hn1 hcn hcl h (lt_of_le_of_lt (le_abs_self y) hyt)
  exact F64SignedRounding.within_of_nonneg 0 y hy0 c (by rw [hlim] at hcl; omega)
    (by rw [hr]; exact Nat.le_add_right _ _) (by rw [hr]; exact Nat.le_add_right _ _)

/-- `WithinSteps 0` for a word whose magnitude lies in binade `n`, not at its start, within half a
spacing of `y`. -/
theorem within_zero_of_close (y : ℝ) (c : UInt64) (hcf : Finite c) (n : ℕ) (hn1 : 1 ≤ n)
    (hcn : n * 2 ^ 52 + 1 ≤ c.toNat % 2 ^ 63) (hcl : c.toNat % 2 ^ 63 + 2 < limit)
    (h : |value c - y| < (2 : ℝ) ^ (n - 1) / 2 ^ 1074 / 2) (hyt : |y| < 2 ^ 1023) :
    F64SignedRounding.WithinSteps 0 y c := by
  have hct := c.toNat_lt
  rcases Nat.lt_or_ge c.toNat (2 ^ 63) with hpos | hneg
  · rw [Nat.mod_eq_of_lt hpos] at hcn hcl
    exact within_zero_pos y c n hn1 hpos hcn hcl h hyt
  · have hnv := F64Magnitude.negate_value c hcf
    have hnt : (Wasm.IEEE64.negate c).toNat = c.toNat % 2 ^ 63 := by
      rw [F64SignedRounding.negate_toNat]
      have hs : Wasm.IEEE64.sign c = true := by
        simp only [Wasm.IEEE64.sign, decide_eq_true_eq]
        exact hneg
      rw [hs, if_pos rfl]
      omega
    have h' : |value (Wasm.IEEE64.negate c) - -y| < (2 : ℝ) ^ (n - 1) / 2 ^ 1074 / 2 := by
      rw [hnv.2, show -value c - -y = -(value c - y) by ring, abs_neg]
      exact h
    exact F64Approx.within_of_negate 0 y c (within_zero_pos (-y) (Wasm.IEEE64.negate c) n hn1
      (by rw [hnt]; omega) (by rw [hnt]; exact hcn) (by rw [hnt]; exact hcl) h'
      (by rw [abs_neg]; exact hyt))

#print axioms reference_of_close
#print axioms within_zero_of_close

end LeanExe.ProofKit.F64WithinZero
