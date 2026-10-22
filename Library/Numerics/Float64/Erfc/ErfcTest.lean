import Library.Numerics.Float64.Erfc.ErfcRound
import LeanExe.ProofKit.F64NearestRelative
import LeanExe.ProofKit.F64Magnitude

/-!
The rounding test of `cr_erfc`.  The fast path returns `left = h + (l - err)` when it equals
`right = h + (l + err)`.  `l - err` and `l + err` round to floats on either side of `l`, so `h + l`
lies between the two exact sums that round to `left` and `right`.  The reals whose nearest float
is a given float form an interval (`near_convex`), so `left` is a nearest float of `h + l`
(`test_near`), whatever the value of `err`.  `near_within` turns a nearest float of `s` with
`|s - y| ≤ (15/16) u y` into one step from `y` (`F64NearestRelative.within_rel_of`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcTest

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft ErfcEft2 ErfcOps ErfcRound F64NearestNonnegative

set_option exponentiation.threshold 2200

/-- `c` is finite and nearest to `s` among all words. -/
def SNear (c : Float) (s : ℝ) : Prop := ff c ∧ ∀ v : UInt64, |fv c - s| ≤ |value v - s|

/-- The points to which `c` is at least as near as `v` form an interval. -/
theorem near_convex (c v s1 s2 s : ℝ) (h1 : |c - s1| ≤ |v - s1|) (h2 : |c - s2| ≤ |v - s2|)
    (hs : (s1 ≤ s ∧ s ≤ s2) ∨ (s2 ≤ s ∧ s ≤ s1)) : |c - s| ≤ |v - s| := by
  have q1 := sq_le_sq.mpr h1
  have q2 := sq_le_sq.mpr h2
  apply sq_le_sq.mp
  rcases le_total c v with hcv | hcv
  · rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hcv) (sub_nonneg.mpr ha)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hcv) (sub_nonneg.mpr ha)]
  · rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hcv) (sub_nonneg.mpr hb)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hcv) (sub_nonneg.mpr hb)]

theorem add_snear (a b : Float) (ha : ff a) (hb : ff b) (hs : |fv a + fv b| ≤ 2 ^ 1022) :
    SNear (a + b) (fv a + fv b) := by
  have h := add_near a.toBits b.toBits ha hb hs
  rw [← F64Bits.toBits_add] at h
  exact h

theorem sub_snear (a b : Float) (ha : ff a) (hb : ff b) (hs : |fv a - fv b| ≤ 2 ^ 1022) :
    SNear (a - b) (fv a - fv b) := by
  have h := sub_near a.toBits b.toBits ha hb hs
  rw [← F64Bits.toBits_sub] at h
  exact h

/-- When the test passes, `left` is a nearest float of `h + l`. -/
theorem test_near (h l err : Float) (hh : ff h) (hl : ff l) (he : ff err) (hb : |fv h| ≤ 4)
    (hlb : |fv l| ≤ 1) (heb : |fv err| ≤ 1) (heq : (h + (l - err) == h + (l + err)) = true) :
    SNear (h + (l - err)) (fv h + fv l) := by
  have k : (2 : ℝ) ^ 4 ≤ 2 ^ 1022 := by norm_num
  have sa := sub_snear l err hl he ((abs_sub_le' _ _).trans (by linarith))
  have sb := add_snear l err hl he ((abs_add_le _ _).trans (by linarith))
  have ha_le : |fv (l - err) - (fv l - fv err)| ≤ |fv err| := by
    have := sa.2 l.toBits
    rwa [show value l.toBits - (fv l - fv err) = fv err by unfold fv; ring] at this
  have hb_le : |fv (l + err) - (fv l + fv err)| ≤ |fv err| := by
    have := sb.2 l.toBits
    rwa [show value l.toBits - (fv l + fv err) = -fv err by unfold fv; ring, abs_neg] at this
  have hfa : |fv (l - err)| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub (fv (l - err)) (fv l - fv err)
    have := abs_sub_le' (fv l) (fv err)
    linarith
  have hfb : |fv (l + err)| ≤ 3 := by
    have := abs_sub_abs_le_abs_sub (fv (l + err)) (fv l + fv err)
    have := abs_add_le (fv l) (fv err)
    linarith
  have sl := add_snear h (l - err) hh sa.1 ((abs_add_le _ _).trans (by linarith))
  have sr := add_snear h (l + err) hh sb.1 ((abs_add_le _ _).trans (by linarith))
  have heqv : fv (h + (l - err)) = fv (h + (l + err)) := (fbeq_iff _ _ sl.1 sr.1).mp heq
  refine ⟨sl.1, fun v => ?_⟩
  have h1 := sl.2 v
  have h2 := sr.2 v
  rw [← heqv] at h2
  refine near_convex _ _ (fv h + fv (l - err)) (fv h + fv (l + err)) _ h1 h2 ?_
  rcases le_total 0 (fv err) with h0 | h0
  · rw [abs_of_nonneg h0] at ha_le hb_le
    left
    constructor <;> linarith [(abs_le.mp ha_le).2, (abs_le.mp hb_le).1]
  · rw [abs_of_nonpos h0] at ha_le hb_le
    right
    constructor <;> linarith [(abs_le.mp ha_le).1, (abs_le.mp hb_le).2]

theorem word_one : Finite (1 : UInt64) ∧ value (1 : UInt64) = 1 / 2 ^ 1074 := by
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
  rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 1 = 1 / 2 ^ 1074 by decide +kernel]
  norm_num

/-- A nearest float of `s` with `|s - y| ≤ (15/16) u y` lies within one step of `y`. -/
theorem near_within (c : Float) (s y : ℝ) (hc : SNear c s) (hy : 1 / 2 ^ 1021 ≤ y)
    (hyt : y < 2 ^ 1022) (hr : |s - y| ≤ 15 / 16 * (1 / 2 ^ 53) * y) :
    F64SignedRounding.WithinSteps 1 y c.toBits := by
  obtain ⟨w1f, w1v⟩ := word_one
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hs : 1 / 2 ^ 1022 ≤ s := by
    have := (abs_le.mp hr).1
    have : 15 / 16 * (1 / 2 ^ 53) * y ≤ y / 2 := by nlinarith
    have : (1 : ℝ) / 2 ^ 1022 = 1 / 2 ^ 1021 / 2 := by norm_num
    linarith
  have hpos : 0 < fv c := by
    have h1 := hc.2 1
    rw [w1v] at h1
    have h2 : |(1 : ℝ) / 2 ^ 1074 - s| = s - 1 / 2 ^ 1074 := by
      rw [abs_of_nonpos (by linarith [show (1 : ℝ) / 2 ^ 1074 ≤ 1 / 2 ^ 1022 by norm_num])]
      ring
    rw [h2] at h1
    have := (abs_le.mp h1).1
    linarith [show (0 : ℝ) < 1 / 2 ^ 1074 by positivity]
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude c.toBits := by
    by_contra h0
    push Not at h0
    have hz : Wasm.IEEE64.scaledMagnitude c.toBits = 0 := by omega
    have : fv c = 0 := by
      simp only [fv, value, Wasm.IEEE64.scaledValue, hz]
      split <;> simp
    linarith
  have hsign : Wasm.IEEE64.sign c.toBits = false := by
    rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign c.toBits) with h | h
    · have := (F64Magnitude.sign_value c.toBits hmag).mp h
      exact absurd this (not_lt.mpr hpos.le)
    · exact h
  have hlim := F64Magnitude.lt_limit_of_finite c.toBits hc.1 hsign
  have hn : Nearest s c.toBits := ⟨hlim, fun v _ => hc.2 v⟩
  refine F64NearestRelative.within_rel_of 1 le_rfl (by norm_num) y s c.toBits hy hyt hn ?_
  rw [show unitRoundoff64 = 1 / 2 ^ 53 from rfl]
  push_cast
  linarith

#print axioms test_near
#print axioms near_within

end Library.Numerics.Float64.Erfc.ErfcTest
