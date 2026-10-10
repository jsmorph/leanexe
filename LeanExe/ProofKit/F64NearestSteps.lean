import LeanExe.ProofKit.F64FullStep
import LeanExe.ProofKit.F64SignedRounding

/-!
One representable step from the nearest word of a nearby number.  Let `c` be a nearest word of
`s` and `w` a nearest word of `y`.  If `c` lay two words above `w`, then `s` would lie above the
midpoint of the two words below `c` and `y` below the midpoint above `w`, so `s - y` would be at
least half the distance from `w` to the second word above it; `step_up` and `step_down` state
this, and `one_step_of_nearest` concludes one step when `s - y` is smaller on both sides.  The
corollaries take `y` in the binade of exponent field `e`, with spacing `d = 2 ^ (e - 1)` scaled
units: `within_of_interior` for `|s - y| < d` with `y` at least two spacings into the binade,
`within_of_relative` for `|s - y|` below `(1 - 2 ^ -50) u y`, and `within_of_tiny` for
`|s - y|` below the smallest spacing.  Each gives `F64SignedRounding.WithinSteps 1 y c`.
-/

namespace LeanExe.ProofKit.F64NearestSteps
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64NearestStep F64PositiveSpacing

set_option exponentiation.threshold 4096
set_option maxRecDepth 100000

theorem word_toNat (n : Nat) (hn : n < limit) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' (hn.trans (by decide : limit < 2 ^ 64))

theorem limit_lt : limit < 2 ^ 63 := by decide

/-- Two words above: `s - y` is at least half the distance from `w` to the second word above. -/
theorem step_up (y s : ℝ) (c w : UInt64) (hc : Nearest s c) (hw : Nearest y w)
    (h2 : w.toNat + 2 ≤ c.toNat) :
    value (UInt64.ofNat (w.toNat + 2)) - value w ≤ 2 * (s - y) := by
  have hcl := hc.1
  have hlim := limit_lt
  have hp : (UInt64.ofNat (c.toNat - 1)).toNat = c.toNat - 1 := word_toNat _ (by omega)
  have hw1 : (UInt64.ofNat (w.toNat + 1)).toNat = w.toNat + 1 := word_toNat _ (by omega)
  have hw2 : (UInt64.ofNat (w.toNat + 2)).toNat = w.toNat + 2 := word_toNat _ (by omega)
  have hPc : value (UInt64.ofNat (c.toNat - 1)) < value c :=
    value_strict (by omega) (by omega)
  have hcs := lower_midpoint _ _ s hPc (hc.2 _ (by omega))
  have hw1v : value w < value (UInt64.ofNat (w.toNat + 1)) :=
    value_strict (by omega) (by omega)
  have hwy := upper_midpoint _ _ y hw1v (hw.2 _ (by omega))
  have hm1 : value (UInt64.ofNat (w.toNat + 1)) ≤ value (UInt64.ofNat (c.toNat - 1)) :=
    (value_le_iff (by omega) (by omega)).mpr (by omega)
  have hm2 : value (UInt64.ofNat (w.toNat + 2)) ≤ value c :=
    (value_le_iff (by omega) (by omega)).mpr (by omega)
  linarith

/-- Two words below: `y - s` is at least half the distance from `w` to the second word below. -/
theorem step_down (y s : ℝ) (c w : UInt64) (hc : Nearest s c) (hw : Nearest y w)
    (h2 : c.toNat + 2 ≤ w.toNat) :
    value w - value (UInt64.ofNat (w.toNat - 2)) ≤ 2 * (y - s) := by
  have hwl := hw.1
  have hcl := hc.1
  have hlim := limit_lt
  have hp : (UInt64.ofNat (c.toNat + 1)).toNat = c.toNat + 1 := word_toNat _ (by omega)
  have hw1 : (UInt64.ofNat (w.toNat - 1)).toNat = w.toNat - 1 := word_toNat _ (by omega)
  have hw2 : (UInt64.ofNat (w.toNat - 2)).toNat = w.toNat - 2 := word_toNat _ (by omega)
  have hcP : value c < value (UInt64.ofNat (c.toNat + 1)) :=
    value_strict (by omega) (by omega)
  have hcs := upper_midpoint _ _ s hcP (hc.2 _ (by omega))
  have hw1v : value (UInt64.ofNat (w.toNat - 1)) < value w :=
    value_strict (by omega) (by omega)
  have hwy := lower_midpoint _ _ y hw1v (hw.2 _ (by omega))
  have hm1 : value (UInt64.ofNat (c.toNat + 1)) ≤ value (UInt64.ofNat (w.toNat - 1)) :=
    (value_le_iff (by omega) (by omega)).mpr (by omega)
  have hm2 : value c ≤ value (UInt64.ofNat (w.toNat - 2)) :=
    (value_le_iff (by omega) (by omega)).mpr (by omega)
  linarith

theorem one_step_of_nearest (y s : ℝ) (c w : UInt64) (hc : Nearest s c) (hw : Nearest y w)
    (hup : w.toNat + 2 < limit →
      2 * (s - y) < value (UInt64.ofNat (w.toNat + 2)) - value w)
    (hdown : 2 ≤ w.toNat → 2 * (y - s) < value w - value (UInt64.ofNat (w.toNat - 2))) :
    c.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ c.toNat + 1 := by
  constructor
  · by_contra h
    have h2 : w.toNat + 2 ≤ c.toNat := by omega
    have := step_up y s c w hc hw h2
    have := hup (by have := hc.1; omega)
    linarith
  · by_contra h
    have h2 : c.toNat + 2 ≤ w.toNat := by omega
    have := step_down y s c w hc hw h2
    have := hdown (by omega)
    linarith

/-- The distance across two words from word `n` on is at least two spacings of binade `a`. -/
theorem two_gaps (n a : Nat) (ha : a * 2 ^ 52 ≤ n) (hn : n + 2 < limit) :
    2 * ((2 : ℝ) ^ (a - 1) / 2 ^ 1074) ≤
      value (UInt64.ofNat (n + 2)) - value (UInt64.ofNat n) := by
  have hl := limit_lt
  have h1 := F64FullStep.gap_lower n a ha (by omega)
  have h2 := F64FullStep.gap_lower (n + 1) a (by omega) (by omega)
  rw [show n + 1 + 1 = n + 2 by omega] at h2
  linarith

/-- From the nonnegative steps to `WithinSteps`. -/
theorem within_of_steps (y : ℝ) (hy : 0 ≤ y) (hyt : y < (2 : ℝ) ^ 1023) (c : UInt64)
    (hc : c.toNat < limit)
    (hsteps : c.toNat ≤ (F64NearestEven.roundNearestEven y).toNat + 1 ∧
      (F64NearestEven.roundNearestEven y).toNat ≤ c.toNat + 1) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hth : y < F64PositiveRounding.overflowThreshold := by
    unfold F64PositiveRounding.overflowThreshold
    have : (2 : ℝ) ^ 1023 ≤ 2 ^ 1024 - 2 ^ 970 := by norm_num
    linarith
  rw [← F64PositiveRounding.reference_finite y hth] at hsteps
  exact F64SignedRounding.within_of_nonneg 1 y hy c (by have := hc; unfold limit at this; omega)
    hsteps.1 hsteps.2

/-- A nearest word of `y` lies at or above every word whose value is at most `y`. -/
theorem nearest_ge (y : ℝ) (w lo : UInt64) (hw : Nearest y w) (hlo : lo.toNat < limit)
    (hyl : value lo ≤ y) : lo.toNat ≤ w.toNat := by
  by_contra hn
  have hlt := value_strict (hlo.trans limit_lt) (show w.toNat < lo.toNat by omega)
  have hd := hw.2 lo hlo
  rw [abs_of_nonpos (by linarith : value w - y ≤ 0),
    abs_of_nonpos (by linarith : value lo - y ≤ 0)] at hd
  linarith

/-- The value of the third word of binade `e`. -/
theorem third_word_value (e : Nat) (he : 1 ≤ e) (he' : e ≤ 2045) :
    value (UInt64.ofNat (e * 2 ^ 52 + 2)) =
      ((2 : ℝ) ^ (e + 51) + 2 * 2 ^ (e - 1)) / 2 ^ 1074 := by
  have hb := boundary_value e he (by omega)
  have g0 := gap_binade (e * 2 ^ 52) e he (by omega) le_rfl (by omega)
  have g1 := gap_binade (e * 2 ^ 52 + 1) e he (by omega) (by omega) (by omega)
  rw [show e * 2 ^ 52 + 1 + 1 = e * 2 ^ 52 + 2 by omega] at g1
  rw [add_div, ← hb]
  linarith

theorem ofNat_toNat_value (w : UInt64) : value (UInt64.ofNat w.toNat) = value w := by
  rw [UInt64.ofNat_toNat]

/-- Arithmetic on word positions, kept apart from facts with large coefficients, on which
`omega` exceeds the recursion limit. -/
theorem below_two (n k L : Nat) (h : k + 2 ≤ n) (hn : n < L) :
    k ≤ n - 2 ∧ n - 2 + 2 < L ∧ n - 2 + 2 = n ∧ k ≤ n ∧ 2 ≤ n := by omega

theorem two_le_of_lt (n L : Nat) (h : 2 ≤ n) (hn : n < L) : n - 2 + 2 < L ∧ n - 2 + 2 = n := by
  omega

theorem boundary_lt_limit (e : Nat) (he' : e ≤ 2045) : e * 2 ^ 52 + 2 < limit := by
  unfold limit
  omega

theorem previous_binade (e : Nat) (he : 2 ≤ e) : (e - 1) * 2 ^ 52 + 2 ≤ e * 2 ^ 52 := by
  have h : e * 2 ^ 52 = (e - 1) * 2 ^ 52 + 2 ^ 52 := by
    rw [← Nat.succ_mul, show (e - 1).succ = e by omega]
  rw [h]
  exact Nat.add_le_add_left (by norm_num) _

/-- The steps for `y` at least two spacings into binade `e`. -/
theorem steps_interior (y s : ℝ) (c w : UInt64) (e : Nat) (he : 1 ≤ e) (he' : e ≤ 2045)
    (hy : ((2 : ℝ) ^ (e + 51) + 2 * 2 ^ (e - 1)) / 2 ^ 1074 ≤ y)
    (hc : Nearest s c) (hw : Nearest y w) (hd : |s - y| < (2 : ℝ) ^ (e - 1) / 2 ^ 1074) :
    c.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ c.toNat + 1 := by
  have hel := boundary_lt_limit e he'
  have hwlo := nearest_ge y _ _ hw (by rw [word_toNat _ hel]; exact hel)
    (by rw [third_word_value e he he']; exact hy)
  rw [word_toNat _ hel] at hwlo
  obtain ⟨hk, hlt, heq, hk', -⟩ := below_two _ _ _ hwlo hw.1
  refine one_step_of_nearest y s c w hc hw ?_ ?_
  · intro hl
    have h := two_gaps w.toNat e hk' hl
    rw [ofNat_toNat_value] at h
    have := (abs_lt.mp hd).2
    linarith
  · intro _
    have h := two_gaps (w.toNat - 2) e hk hlt
    rw [heq, ofNat_toNat_value] at h
    have := (abs_lt.mp hd).1
    linarith

/-- Within one step when `|s - y|` is below the spacing `d = 2 ^ (e - 1)` scaled units of the
binade of `y` and `y` lies at least two spacings above the start of the binade. -/
theorem within_of_interior (y s : ℝ) (c : UInt64) (e : Nat) (he : 1 ≤ e) (he' : e ≤ 2045)
    (hy : ((2 : ℝ) ^ (e + 51) + 2 * 2 ^ (e - 1)) / 2 ^ 1074 ≤ y) (hyt : y < (2 : ℝ) ^ 1023)
    (hc : Nearest s c) (hd : |s - y| < (2 : ℝ) ^ (e - 1) / 2 ^ 1074) :
    F64SignedRounding.WithinSteps 1 y c :=
  within_of_steps y (le_trans (by positivity) hy) hyt c hc.1
    (steps_interior y s c _ e he he' hy hc (F64NearestEven.roundNearestEven_spec y).1 hd)

/-- The steps for `y` in binade `e` with relative distance below `(1 - 2 ^ -50) u`. -/
theorem steps_relative (y s : ℝ) (c w : UInt64) (e : Nat) (he : 1 ≤ e) (he' : e ≤ 2045)
    (hy : (2 : ℝ) ^ (e + 51) / 2 ^ 1074 ≤ y) (hy' : y < (2 : ℝ) ^ (e + 52) / 2 ^ 1074)
    (hc : Nearest s c) (hw : Nearest y w)
    (hr : |s - y| ≤ (1 - 1 / 2 ^ 50) * unitRoundoff64 * y) :
    c.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ c.toNat + 1 := by
  set P : ℝ := (2 : ℝ) ^ (e - 1) with hP
  have hP0 : 0 < P := by positivity
  have h51 : (2 : ℝ) ^ (e + 51) = 2 ^ 52 * P := by
    rw [hP, ← pow_add]; congr 1; omega
  have h52 : (2 : ℝ) ^ (e + 52) = 2 ^ 53 * P := by
    rw [hP, ← pow_add]; congr 1; omega
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hT : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have hd : |s - y| < P / 2 ^ 1074 := by
    refine hr.trans_lt ?_
    rw [h52, lt_div_iff₀ hT] at hy'
    rw [hu, lt_div_iff₀ hT]
    have hpos : (0 : ℝ) ≤ y * 2 ^ 1074 := by positivity
    nlinarith
  have hel2 := boundary_lt_limit e he'
  have hel : e * 2 ^ 52 < limit := lt_of_le_of_lt (Nat.le_add_right _ _) hel2
  have hwlo := nearest_ge y _ _ hw (by rw [word_toNat _ hel]; exact hel)
    (by rw [boundary_value e he (by omega)]; exact hy)
  rw [word_toNat _ hel] at hwlo
  have hwl := hw.1
  refine one_step_of_nearest y s c w hc hw ?_ ?_
  · intro hl
    have h := two_gaps w.toNat e hwlo hl
    rw [ofNat_toNat_value] at h
    have := (abs_lt.mp hd).2
    linarith
  · intro h2
    obtain ⟨hlt, heq⟩ := two_le_of_lt _ _ h2 hwl
    have hdown : P / 2 ^ 1074 ≤ value w - value (UInt64.ofNat (w.toNat - 2)) := by
      rcases Nat.lt_or_ge e 2 with he1 | he2
      · have h := two_gaps (w.toNat - 2) 0 (Nat.zero_le _) hlt
        rw [heq, ofNat_toNat_value] at h
        have hPe : P = 1 := by rw [hP, show e - 1 = 0 by omega, pow_zero]
        rw [hPe]
        have h1 : (1 : ℝ) / 2 ^ 1074 ≤ 2 * ((2 : ℝ) ^ (0 - 1) / 2 ^ 1074) := by norm_num
        linarith
      · have hm := previous_binade e he2
        have h := two_gaps (w.toNat - 2) (e - 1)
          ((below_two _ _ _ (le_trans hm hwlo) hwl).1) hlt
        rw [heq, ofNat_toNat_value] at h
        have hpe : (2 : ℝ) * 2 ^ (e - 1 - 1) = P := by
          rw [hP, ← pow_succ']; congr 1; omega
        have h1 : P / 2 ^ 1074 = 2 * ((2 : ℝ) ^ (e - 1 - 1) / 2 ^ 1074) := by
          rw [← hpe]; ring
        linarith
    rcases Nat.lt_or_ge w.toNat (e * 2 ^ 52 + 2) with hwl2 | hwl2
    · have hyb : y < ((2 : ℝ) ^ (e + 51) + 2 * 2 ^ (e - 1)) / 2 ^ 1074 := by
        by_contra hn
        have := nearest_ge y _ _ hw (by rw [word_toNat _ hel2]; exact hel2)
          (by rw [third_word_value e he he']; exact not_lt.mp hn)
        rw [word_toNat _ hel2] at this
        exact absurd this (not_le.mpr hwl2)
      have hys : y - s < P / 2 ^ 1074 / 2 := by
        have h1 := (abs_le.mp hr).1
        rw [h51, ← hP, lt_div_iff₀ hT] at hyb
        rw [hu] at h1
        rw [div_div, lt_div_iff₀ (by positivity)]
        have hpos : (0 : ℝ) ≤ y * 2 ^ 1074 := by positivity
        nlinarith
      linarith
    · have h := two_gaps (w.toNat - 2) e ((below_two _ _ _ hwl2 hwl).1) hlt
      rw [heq, ofNat_toNat_value] at h
      have := (abs_lt.mp hd).1
      linarith

/-- Within one step when `|s - y|` is below `(1 - 2 ^ -50) u y` for `y` in the binade of exponent
field `e`. -/
theorem within_of_relative (y s : ℝ) (c : UInt64) (e : Nat) (he : 1 ≤ e) (he' : e ≤ 2045)
    (hy : (2 : ℝ) ^ (e + 51) / 2 ^ 1074 ≤ y) (hy' : y < (2 : ℝ) ^ (e + 52) / 2 ^ 1074)
    (hc : Nearest s c) (hr : |s - y| ≤ (1 - 1 / 2 ^ 50) * unitRoundoff64 * y) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hyt : y < (2 : ℝ) ^ 1023 := by
    refine hy'.trans_le ?_
    rw [div_le_iff₀ (by positivity), ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact within_of_steps y (le_trans (by positivity) hy) hyt c hc.1
    (steps_relative y s c _ e he he' hy hy' hc (F64NearestEven.roundNearestEven_spec y).1 hr)

/-- The steps when `|s - y|` is below the smallest spacing. -/
theorem steps_tiny (y s : ℝ) (c w : UInt64) (hc : Nearest s c) (hw : Nearest y w)
    (hd : |s - y| < 1 / 2 ^ 1074) :
    c.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ c.toNat + 1 := by
  have hwl := hw.1
  have h0 : (1 : ℝ) / 2 ^ 1074 ≤ 2 ^ (0 - 1) / 2 ^ 1074 := by norm_num
  refine one_step_of_nearest y s c w hc hw ?_ ?_
  · intro hl
    have h := two_gaps w.toNat 0 (Nat.zero_le _) hl
    rw [ofNat_toNat_value] at h
    have := (abs_lt.mp hd).2
    linarith
  · intro h2
    obtain ⟨hlt, heq⟩ := two_le_of_lt _ _ h2 hwl
    have h := two_gaps (w.toNat - 2) 0 (Nat.zero_le _) hlt
    rw [heq, ofNat_toNat_value] at h
    have := (abs_lt.mp hd).1
    linarith

/-- Within one step when `|s - y|` is below the smallest spacing. -/
theorem within_of_tiny (y s : ℝ) (c : UInt64) (hy0 : 0 ≤ y) (hyt : y < (2 : ℝ) ^ 1023)
    (hc : Nearest s c) (hd : |s - y| < 1 / 2 ^ 1074) :
    F64SignedRounding.WithinSteps 1 y c :=
  within_of_steps y hy0 hyt c hc.1
    (steps_tiny y s c _ hc (F64NearestEven.roundNearestEven_spec y).1 hd)

#print axioms step_up
#print axioms step_down
#print axioms one_step_of_nearest
#print axioms within_of_steps
#print axioms within_of_interior
#print axioms within_of_relative
#print axioms within_of_tiny

end LeanExe.ProofKit.F64NearestSteps
