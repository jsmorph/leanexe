import LeanExe.ProofKit.F64NearestSteps

/-!
One step from a band around `y` that is wider below than `F64NearestSteps.steps_half` allows.
Let `y` lie in the binade of exponent field `e ≥ 2`, with spacing `d = 2 ^ (e - 1)` scaled units,
let `c` be a nearest word of `s` and `w` one of `y`.  If `s - y < d` and `y - s < 3d/4`, then `c`
and `w` lie within one word of each other (`steps_band`).  Two words above `w` would put `s` at
least a spacing above `y`.  Two words below `w` would put `s` below the midpoint of the two words
under `w - 1`.  When `w` is the first word of the binade, those words lie in the binade below,
where the spacing is `d/2`, so `s ≤ y - 3d/4` because `y` is at least the first word.  Otherwise
`w - 1` is at least the first word, and the distance from `w - 2` to `w` is at least `3d/2`.
-/

namespace LeanExe.ProofKit.F64NearestBand
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64NearestStep F64PositiveSpacing
  F64NearestSteps

set_option exponentiation.threshold 4096
set_option maxRecDepth 100000

theorem positions (n e : Nat) (he : 2 ≤ e) (hn : e * 2 ^ 52 ≤ n) :
    (e - 1) * 2 ^ 52 ≤ n - 1 ∧ (e - 1) * 2 ^ 52 ≤ n - 2 ∧ n - 1 + 1 = n ∧ n - 2 + 1 = n - 1 := by
  have h := previous_binade e he
  omega

theorem above_first (n e L : Nat) (hn : e * 2 ^ 52 + 1 ≤ n) (hnL : n < L) (hL : L < 2 ^ 63) :
    e * 2 ^ 52 ≤ n - 1 ∧ n - 1 + 1 < 2 ^ 63 ∧ n - 2 + 1 < 2 ^ 63 := by
  omega

theorem half_spacing (e : Nat) (he : 2 ≤ e) :
    (2 : ℝ) ^ (e - 1 - 1) / 2 ^ 1074 = (2 : ℝ) ^ (e - 1) / 2 ^ 1074 / 2 := by
  have h : (2 : ℝ) ^ (e - 1) = 2 ^ (e - 1 - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [h]; ring

theorem steps_band (y s : ℝ) (c w : UInt64) (e : Nat) (he : 2 ≤ e) (he' : e ≤ 2046)
    (hy : (2 : ℝ) ^ (e + 51) / 2 ^ 1074 ≤ y) (hc : Nearest s c) (hw : Nearest y w)
    (hup : s - y < (2 : ℝ) ^ (e - 1) / 2 ^ 1074)
    (hdown : y - s < 3 / 4 * ((2 : ℝ) ^ (e - 1) / 2 ^ 1074)) :
    c.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ c.toNat + 1 := by
  have hel2 := boundary_lt_limit e he'
  have hel : e * 2 ^ 52 < limit := lt_of_le_of_lt (Nat.le_add_right _ _) hel2
  have hB := boundary_value e (by omega) (by omega)
  have hwlo := nearest_ge y _ _ hw (by rw [word_toNat _ hel]; exact hel) (by rw [hB]; exact hy)
  rw [word_toNat _ hel] at hwlo
  have hwl := hw.1
  have hcl := hc.1
  have hlim := limit_lt
  have hhalf := half_spacing e he
  constructor
  · by_contra h
    have h2 : w.toNat + 2 ≤ c.toNat := by omega
    have h1 := step_up y s c w hc hw h2
    have h3 := two_gaps w.toNat e hwlo (by omega)
    rw [ofNat_toNat_value] at h3
    linarith
  · by_contra h
    have h2 : c.toNat + 2 ≤ w.toNat := by omega
    obtain ⟨p1, p2, p3, p4⟩ := positions w.toNat e he hwlo
    rcases Nat.lt_or_ge w.toNat (e * 2 ^ 52 + 1) with hw0 | hw1
    · have hwB : w.toNat = e * 2 ^ 52 := by omega
      have hp : (UInt64.ofNat (c.toNat + 1)).toNat = c.toNat + 1 := word_toNat _ (by omega)
      have hb1 : (UInt64.ofNat (w.toNat - 1)).toNat = w.toNat - 1 := word_toNat _ (by omega)
      have hb2 : (UInt64.ofNat (w.toNat - 2)).toNat = w.toNat - 2 := word_toNat _ (by omega)
      have hcP : value c < value (UInt64.ofNat (c.toNat + 1)) :=
        value_strict (by omega) (by omega)
      have hcs := upper_midpoint _ _ s hcP (hc.2 _ (by omega))
      have hm1 : value (UInt64.ofNat (c.toNat + 1)) ≤ value (UInt64.ofNat (w.toNat - 1)) :=
        (value_le_iff (by omega) (by omega)).mpr (by omega)
      have hm2 : value c ≤ value (UInt64.ofNat (w.toNat - 2)) :=
        (value_le_iff (by omega) (by omega)).mpr (by omega)
      have g1 := F64FullStep.gap_lower (w.toNat - 1) (e - 1) p1 (by omega)
      have g2 := F64FullStep.gap_lower (w.toNat - 2) (e - 1) p2 (by omega)
      rw [p3, ofNat_toNat_value] at g1
      rw [p4] at g2
      have hwv : value w = (2 : ℝ) ^ (e + 51) / 2 ^ 1074 := by
        rw [← hB, ← hwB, ofNat_toNat_value]
      linarith
    · have h1 := step_down y s c w hc hw h2
      obtain ⟨q1, q2, q3⟩ := above_first w.toNat e _ hw1 hwl limit_lt
      have g1 := F64FullStep.gap_lower (w.toNat - 1) e q1 q2
      have g2 := F64FullStep.gap_lower (w.toNat - 2) (e - 1) p2 q3
      rw [p3, ofNat_toNat_value] at g1
      rw [p4] at g2
      linarith

/-- `WithinSteps 1` from the band of `steps_band`. -/
theorem within_of_band (y s : ℝ) (c : UInt64) (e : Nat) (he : 2 ≤ e) (he' : e ≤ 2046)
    (hy : (2 : ℝ) ^ (e + 51) / 2 ^ 1074 ≤ y) (hyt : y < F64PositiveRounding.overflowThreshold)
    (hc : Nearest s c) (hup : s - y < (2 : ℝ) ^ (e - 1) / 2 ^ 1074)
    (hdown : y - s < 3 / 4 * ((2 : ℝ) ^ (e - 1) / 2 ^ 1074)) :
    F64SignedRounding.WithinSteps 1 y c :=
  within_of_steps y (le_trans (by positivity) hy) hyt c hc.1
    (steps_band y s c _ e he he' hy hc (F64NearestEven.roundNearestEven_spec y).1 hup hdown)

#print axioms steps_band
#print axioms within_of_band

end LeanExe.ProofKit.F64NearestBand
