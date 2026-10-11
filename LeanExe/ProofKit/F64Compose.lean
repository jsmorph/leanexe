import LeanExe.ProofKit.F64TwoSteps

/-!
Composition of step bounds.  A word within one step of the reference of `y₁` lies within two
steps of the reference of `y₂` when `y₁` and `y₂` are positive and closer than one spacing of a
binade whose start lies below both: their nearest words are then at most one step apart
(`F64RoundNearest.steps_of_nearest`).  This composes a library call that is within one step of
its own exact value, at a computed argument, with the error of that argument.
-/

namespace LeanExe.ProofKit.F64Compose
open CodeLib.IEEE64 F64NearestNonnegative

set_option exponentiation.threshold 4096

theorem within_two_of_close (y₁ y₂ : ℝ) (c : UInt64) (h : F64SignedRounding.WithinSteps 1 y₁ c)
    (a : ℕ) (ha1 : 1 ≤ a) (ha : a < 2047)
    (h₁ : value (UInt64.ofNat (a * 2 ^ 52)) ≤ y₁) (h₂ : value (UInt64.ofNat (a * 2 ^ 52)) ≤ y₂)
    (hd : |y₁ - y₂| < (2 : ℝ) ^ (a - 1) / 2 ^ 1074)
    (ht₁ : y₁ < F64PositiveRounding.overflowThreshold)
    (ht₂ : y₂ < F64PositiveRounding.overflowThreshold) :
    F64SignedRounding.WithinSteps 2 y₂ c := by
  have hB := F64PositiveSpacing.boundary_value a ha1 (by omega)
  have hB0 : 0 < value (UInt64.ofNat (a * 2 ^ 52)) := by rw [hB]; positivity
  have hy₁ : 0 ≤ y₁ := by linarith
  have hy₂ : 0 ≤ y₂ := by linarith
  obtain ⟨hcn, hcp⟩ := h
  have hr₁ : F64SignedRounding.roundNearestEven y₁ = F64PositiveRounding.roundNearestEven y₁ := by
    simp only [F64SignedRounding.roundNearestEven, if_pos hy₁]
  rw [hr₁] at hcp
  have hw₁ := (F64NearestEven.roundNearestEven_spec y₁).1
  have hw₂ := (F64NearestEven.roundNearestEven_spec y₂).1
  rw [← F64PositiveRounding.reference_finite y₁ ht₁] at hw₁
  rw [← F64PositiveRounding.reference_finite y₂ ht₂] at hw₂
  have hst := F64RoundNearest.steps_of_nearest y₁ y₂ _ _ hw₁ hw₂ a ha h₁ h₂ hd
  have hra := F64RoundNearest.nearest_above y₁ _ hw₁ a ha h₁
  have hp₁ := F64SignedRounding.positive_reference_le y₁
  rw [F64SignedRounding.position_of_lt (F64PositiveRounding.roundNearestEven y₁) (by omega)] at hcp
  have hcp' := abs_le.mp hcp
  have hc63 : c.toNat < 2 ^ 63 := by
    by_contra hge
    push Not at hge
    have hneg : F64SignedRounding.position c = -((c.toNat - 2 ^ 63 : ℕ) : ℤ) := by
      simp only [F64SignedRounding.position, Wasm.IEEE64.sign, decide_eq_true hge,
        ite_true]
    rw [hneg] at hcp'
    omega
  rw [F64SignedRounding.position_of_lt _ hc63] at hcp'
  exact F64SignedRounding.within_of_nonneg 2 y₂ hy₂ c (by omega) (by omega) (by omega)

/-- The word `n 2 ^ 52 + j` of binade `n` has value `2 ^ (n - 1023) + j` spacings. -/
theorem binade_word (n j : ℕ) (hn1 : 1 ≤ n) (hn : n + 1 < 2048) (hj : j ≤ 2 ^ 52) :
    value (UInt64.ofNat (n * 2 ^ 52 + j)) =
      (2 : ℝ) ^ (n + 51) / 2 ^ 1074 + j * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074) := by
  induction j with
  | zero =>
    simp only [add_zero, Nat.cast_zero, zero_mul]
    exact F64PositiveSpacing.boundary_value n hn1 (by omega)
  | succ j ih =>
    have h1 := ih (by omega)
    have hg := F64PositiveSpacing.gap_binade (n * 2 ^ 52 + j) n hn1 hn (by omega) (by omega)
    rw [← Nat.add_assoc]
    push_cast
    linarith

/-- The error of a word within one step of the reference of `y` in binade `n`: at most two and a
half spacings, and one and a half when `y` lies two spacings or more below the next binade. -/
theorem error_of_within (y : ℝ) (c : UInt64) (h : F64SignedRounding.WithinSteps 1 y c) (n : ℕ)
    (hn2 : 2 ≤ n) (hn : n + 2 < 2048)
    (hy1 : (2 : ℝ) ^ (n + 51) / 2 ^ 1074 ≤ y) (hy2 : y < 2 * ((2 : ℝ) ^ (n + 51) / 2 ^ 1074)) :
    |value c - y| ≤ 5 / 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074) ∧
      (y + 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074) ≤ 2 * ((2 : ℝ) ^ (n + 51) / 2 ^ 1074) →
        |value c - y| ≤ 3 / 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074)) := by
  have hW := fun j (hj : j ≤ 2 ^ 52) => binade_word n j (by omega) (by omega) hj
  set sp := (2 : ℝ) ^ (n - 1) / 2 ^ 1074 with hsp
  set B := (2 : ℝ) ^ (n + 51) / 2 ^ 1074 with hB
  have hsp0 : 0 < sp := by positivity
  have hBsp : B = 2 ^ 52 * sp := by
    rw [hB, hsp, show n + 51 = (n - 1) + 52 by omega, pow_add]
    ring
  have hy0 : 0 ≤ y := le_trans (by positivity) hy1
  have hyt : y < F64PositiveRounding.overflowThreshold := by
    have h3 : (2 : ℝ) ^ (n + 51) ≤ 2 ^ 2096 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : 2 * ((2 : ℝ) ^ 2096 / 2 ^ 1074) < F64PositiveRounding.overflowThreshold := by
      rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - 2 ^ 970 from rfl]
      norm_num
    have h5 : B ≤ (2 : ℝ) ^ 2096 / 2 ^ 1074 := div_le_div_of_nonneg_right h3 (by positivity)
    linarith
  have hlim : F64NearestNonnegative.limit = 2047 * 2 ^ 52 := rfl
  have hofNat : ∀ k : ℕ, k < 2 ^ 63 → (UInt64.ofNat k).toNat = k := fun k hk =>
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  set r := F64PositiveRounding.roundNearestEven y with hrd
  have hw : Nearest y r := by
    rw [hrd, F64PositiveRounding.reference_finite y hyt]
    exact (F64NearestEven.roundNearestEven_spec y).1
  have hB0w := F64PositiveSpacing.boundary_value n (by omega) (by omega)
  have hr1 := F64RoundNearest.nearest_above y r hw n (by omega) (by rw [hB0w]; exact hy1)
  have hr2 : r.toNat ≤ (n + 1) * 2 ^ 52 := by
    have h3 := F64PositiveOrder.nearest_interval y r (UInt64.ofNat (n * 2 ^ 52))
      (UInt64.ofNat ((n + 1) * 2 ^ 52)) hw (by rw [hofNat _ (by omega), hlim]; omega)
      (by rw [hofNat _ (by omega), hlim]; omega) (by rw [hB0w]; exact hy1)
      (by
        rw [F64PositiveSpacing.boundary_value (n + 1) (by omega) (by omega),
          show n + 1 + 51 = (n + 51) + 1 by omega, pow_succ]
        have h4 : (2 : ℝ) ^ (n + 51) * 2 / 2 ^ 1074 = 2 * B := by rw [hB]; ring
        rw [h4]
        exact hy2.le)
    rw [hofNat (n * 2 ^ 52) (by omega), hofNat ((n + 1) * 2 ^ 52) (by omega)] at h3
    exact h3.2
  obtain ⟨j, hj⟩ : ∃ j, r.toNat = n * 2 ^ 52 + j := ⟨r.toNat - n * 2 ^ 52, by omega⟩
  have hjle : j ≤ 2 ^ 52 := by
    have : (n + 1) * 2 ^ 52 = n * 2 ^ 52 + 2 ^ 52 := by ring
    omega
  have hrw : r = UInt64.ofNat r.toNat := UInt64.ofNat_toNat.symm
  have hrv : value r = B + j * sp := by
    rw [hrw, hj]
    exact hW j hjle
  -- the reference lies within half a spacing of `y`
  have hry : |value r - y| ≤ sp / 2 := by
    rcases le_or_gt y (value r) with hle | hgt
    · rw [abs_of_nonneg (by linarith)]
      rcases Nat.eq_zero_or_pos j with hj0 | hjp
      · rw [hj0, Nat.cast_zero, zero_mul, add_zero] at hrv
        linarith
      · have hv := hw.2 (UInt64.ofNat (n * 2 ^ 52 + (j - 1)))
          (by rw [hofNat _ (by omega), hlim]; omega)
        rw [hW (j - 1) (by omega), abs_of_nonneg (by linarith : 0 ≤ value r - y),
          Nat.cast_sub hjp, Nat.cast_one] at hv
        rcases abs_cases (B + (↑j - 1) * sp - y) with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at hv <;>
          linarith
    · rw [abs_of_neg (by linarith)]
      have hjl : j < 2 ^ 52 := by
        by_contra hc
        have : j = 2 ^ 52 := by omega
        rw [this] at hrv
        push_cast at hrv
        linarith
      have hv := hw.2 (UInt64.ofNat (n * 2 ^ 52 + (j + 1)))
        (by rw [hofNat _ (by omega), hlim]; omega)
      rw [hW (j + 1) (by omega), abs_of_neg (by linarith : value r - y < 0)] at hv
      push_cast at hv
      rcases abs_cases (B + (↑j + 1) * sp - y) with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha] at hv <;>
        linarith
  -- the position of `c`
  obtain ⟨hcn, hcp⟩ := h
  have hr63 : r.toNat < 2 ^ 63 := by omega
  have hrr : F64SignedRounding.roundNearestEven y = r := by
    simp only [F64SignedRounding.roundNearestEven, if_pos hy0, hrd]
  rw [hrr, F64SignedRounding.position_of_lt r hr63] at hcp
  have hcp' := abs_le.mp hcp
  have hc63 : c.toNat < 2 ^ 63 := by
    by_contra hge
    push Not at hge
    have hneg : F64SignedRounding.position c = -((c.toNat - 2 ^ 63 : ℕ) : ℤ) := by
      simp only [F64SignedRounding.position, Wasm.IEEE64.sign, decide_eq_true hge, ite_true]
    rw [hneg] at hcp'
    omega
  rw [F64SignedRounding.position_of_lt c hc63] at hcp'
  have hcw : value c = value (UInt64.ofNat c.toNat) := by rw [UInt64.ofNat_toNat]
  -- the value of `c`
  have hcs : value c - value r ≤ sp ∨ (j = 2 ^ 52 ∧ value c - value r ≤ 2 * sp) := by
    rcases (by omega : c.toNat ≤ r.toNat ∨ c.toNat = r.toNat + 1) with hc | hc
    · left
      have := (F64PositiveOrder.value_le_iff hc63 hr63).mpr hc
      linarith
    · rcases Nat.lt_or_ge j (2 ^ 52) with hjl | hjg
      · left
        rw [hcw, hc, hj, Nat.add_assoc, hW (j + 1) (by omega)]
        push_cast
        linarith
      · right
        refine ⟨by omega, ?_⟩
        have hj2 : j = 2 ^ 52 := by omega
        have hg := F64PositiveSpacing.gap_binade ((n + 1) * 2 ^ 52) (n + 1) (by omega) (by omega)
          le_rfl (by ring_nf; omega)
        have htop : value (UInt64.ofNat ((n + 1) * 2 ^ 52)) = value r := by
          rw [hrw, hj, hj2, show n * 2 ^ 52 + 2 ^ 52 = (n + 1) * 2 ^ 52 by ring]
        have h2sp : (2 : ℝ) ^ (n + 1 - 1) / 2 ^ 1074 = 2 * sp := by
          rw [hsp, show n + 1 - 1 = (n - 1) + 1 by omega,
            show (2 : ℝ) ^ ((n - 1) + 1) = 2 ^ (n - 1) * 2 from pow_succ 2 (n - 1)]
          ring
        have hgap := hg.trans h2sp
        rw [hcw, hc, hj, hj2, show n * 2 ^ 52 + 2 ^ 52 + 1 = (n + 1) * 2 ^ 52 + 1 by ring, ← htop]
        exact hgap.le
  have hci : value r - value c ≤ sp := by
    rcases (by omega : r.toNat ≤ c.toNat ∨ c.toNat + 1 = r.toNat) with hc | hc
    · have := (F64PositiveOrder.value_le_iff hr63 hc63).mpr hc
      linarith
    · rcases Nat.eq_zero_or_pos j with hj0 | hjp
      · have hg := F64PositiveSpacing.gap_binade (n * 2 ^ 52 - 1) (n - 1) (by omega) (by omega)
          (by rw [Nat.sub_mul]; omega) (by rw [Nat.sub_add_cancel (by omega)]; omega)
        rw [Nat.sub_add_cancel (by omega)] at hg
        have hrb : value (UInt64.ofNat (n * 2 ^ 52)) = value r := by
          rw [hrw, hj, hj0, add_zero]
        have hcb : value c = value (UInt64.ofNat (n * 2 ^ 52 - 1)) := by
          rw [hcw]
          congr 2
          omega
        rw [hcb, ← hrb]
        have h3 : (2 : ℝ) ^ (n - 1 - 1) / 2 ^ 1074 ≤ sp := by
          rw [hsp]
          exact div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega))
            (by positivity)
        exact (le_of_eq hg).trans h3
      · have hcb : value c = B + (↑j - 1) * sp := by
          rw [hcw, show c.toNat = n * 2 ^ 52 + (j - 1) by omega, hW (j - 1) (by omega),
            Nat.cast_sub hjp, Nat.cast_one]
        rw [hcb, hrv]
        linarith
  constructor
  · rw [abs_le] at hry ⊢
    rcases hcs with hcs | ⟨-, hcs⟩ <;> constructor <;> linarith [hry.1, hry.2]
  · intro htop
    have hjl : j < 2 ^ 52 := by
      by_contra hc
      have hj2 : j = 2 ^ 52 := by omega
      rw [hj2] at hrv
      push_cast at hrv
      have := (abs_le.mp hry).2
      linarith
    rcases hcs with hcs | ⟨hj2, -⟩
    · rw [abs_le] at hry ⊢
      constructor <;> linarith [hry.1, hry.2]
    · omega

#print axioms within_two_of_close
#print axioms error_of_within

end LeanExe.ProofKit.F64Compose
