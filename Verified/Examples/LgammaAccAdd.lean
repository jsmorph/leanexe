import Verified.Examples.LgammaAccLow

/-!
The addition of a logarithm `lh + ll + lll` to a triple `fh + fl + fll` in the windows of
`Lgamma.accurate` from `1/4` to `15/4`: `sumDD` of the low parts, `twoSum` of the high parts, and
`sumDD` of the new low part with the low part of the `twoSum` (`addLog`).  The `twoSum` is exact,
and each `sumDD` adds about `2^-53` of its low parts and `2^-105` of its high part (`addLog_spec`),
so the error stays near `2^-53` of the low parts and `2^-150` of the high part.
-/

namespace Verified.Examples.LgammaAccAdd
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD

set_option exponentiation.threshold 4096

/-- `(fh, fl, fll) + (lh, ll, lll)` as the windows of `Lgamma.accurate` compute it. -/
def addLog (fh fl fll lh ll lll : Float) : Float × Float × Float :=
  let (fl, fll) := sumDD fl fll ll lll
  let (fh, lh) := twoSum fh lh
  let (fl, fll) := sumDD fl fll lh 0.0
  (fh, fl, fll)

theorem zero_finite : Finite (0.0 : Float).toBits := by
  rw [show (0.0 : Float).toBits = 0 from rfl]; unfold CodeLib.IEEE64.Finite; decide

theorem zero_value : value (0.0 : Float).toBits = 0 := by
  rw [show (0.0 : Float).toBits = 0 from rfl, ← PolyBound.ratOfWord_cast,
    show PolyBound.ratOfWord 0 = 0 by decide +kernel]
  norm_num

set_option maxHeartbeats 4000000 in
/-- **`addLog`**: the high part adds exactly, and the error is
`(7 L1 + B/2^47 + |fh'|/2^100)/2^53` for the high part `fh'` of the result, with `|fl| + |ll| ≤ B`
and `|fll| + |lll| ≤ L1`. -/
theorem addLog_spec (fh fl fll lh ll lll : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (hfll : Finite fll.toBits) (hlh : Finite lh.toBits)
    (hll : Finite ll.toBits) (hlll : Finite lll.toBits) (A B L1 : ℝ)
    (hA : |value fh.toBits| + |value lh.toBits| ≤ A) (hA' : A ≤ 2 ^ 10)
    (hB : |value fl.toBits| + |value ll.toBits| ≤ B) (hB' : B ≤ 1)
    (hL : |value fll.toBits| + |value lll.toBits| ≤ L1) (hL' : L1 ≤ 1) :
    Finite (addLog fh fl fll lh ll lll).1.toBits ∧
      Finite (addLog fh fl fll lh ll lll).2.1.toBits ∧
      Finite (addLog fh fl fll lh ll lll).2.2.toBits ∧
      |value (addLog fh fl fll lh ll lll).1.toBits + value (addLog fh fl fll lh ll lll).2.1.toBits +
          value (addLog fh fl fll lh ll lll).2.2.toBits -
          (value fh.toBits + value fl.toBits + value fll.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits))| ≤
        (7 * L1 + B / 2 ^ 47 + |value (addLog fh fl fll lh ll lll).1.toBits| / 2 ^ 100) / 2 ^ 53 +
          1 / 2 ^ 1100 ∧
      |value (addLog fh fl fll lh ll lll).1.toBits| ≤ |value fh.toBits + value lh.toBits| *
        (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ∧
      |value (addLog fh fl fll lh ll lll).2.1.toBits| ≤
        (B + |value (addLog fh fl fll lh ll lll).1.toBits| / 2 ^ 52) * (1 + 1 / 2 ^ 49) +
          1 / 2 ^ 1070 ∧
      |value (addLog fh fl fll lh ll lll).2.2.toBits| ≤ (L1 + B / 2 ^ 50) * (1 + 1 / 2 ^ 49) +
        |value (addLog fh fl fll lh ll lll).2.1.toBits| / 2 ^ 51 + 1 / 2 ^ 1070 := by
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  have hL0 : 0 ≤ L1 := le_trans (by positivity) hL
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  unfold addLog
  -- `sumDD fl fll ll lll`
  have hl1 : |value fll.toBits| + |value lll.toBits| ≤ L1 := hL
  obtain ⟨a1f, b1f, e1, hb1, ha1⟩ := sumDD_spec fl fll ll lll hfl hfll hll hlll
    (by linarith [abs_nonneg (value ll.toBits), (by norm_num : (1 : ℝ) < 2 ^ 898)])
    (by linarith [abs_nonneg (value fl.toBits), (by norm_num : (1 : ℝ) < 2 ^ 898)])
    L1 hl1 (by linarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 800)])
  generalize sumDD fl fll ll lll = S at a1f b1f e1 hb1 ha1
  obtain ⟨a1, b1⟩ := S
  dsimp only at a1f b1f e1 hb1 ha1 ⊢
  have ha1' : |value a1.toBits| ≤ B * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 := by
    have := abs_add_le (value fl.toBits) (value ll.toBits)
    have := mul_le_mul_of_nonneg_right (this.trans hB) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    linarith
  -- `twoSum fh lh`
  obtain ⟨hf, lf, hsum, hlo⟩ := twoSum_spec fh lh hfh hlh
    (by linarith [abs_nonneg (value lh.toBits), (by norm_num : (2 : ℝ) ^ 10 < 2 ^ 900)])
    (by linarith [abs_nonneg (value fh.toBits), (by norm_num : (2 : ℝ) ^ 10 < 2 ^ 900)])
  generalize twoSum fh lh = P at hf lf hsum hlo
  obtain ⟨h2, l2⟩ := P
  dsimp only at hf lf hsum hlo ⊢
  have hh2 : |value h2.toBits| ≤ |value fh.toBits + value lh.toBits| * (1 + 1 / 2 ^ 51) +
      1 / 2 ^ 1073 := high_bound h2 l2 _ hsum hlo
  have hh2A : |value h2.toBits| ≤ 2 ^ 11 := by
    have := abs_add_le (value fh.toBits) (value lh.toBits)
    have := mul_le_mul_of_nonneg_right (this.trans (hA.trans hA'))
      (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    linarith [(by norm_num : (2 : ℝ) ^ 10 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 2 ^ 11)]
  -- `sumDD a1 b1 l2 0`
  have hl3 : |value b1.toBits| + |value (0.0 : Float).toBits| ≤
      L1 * (1 + 1 / 2 ^ 51) + |value a1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 := by
    rw [zero_value, abs_zero, add_zero]; exact hb1
  have hL3 : L1 * (1 + 1 / 2 ^ 51) + |value a1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 2 ^ 800 := by
    have : |value a1.toBits| ≤ 2 := by
      linarith [(by norm_num : (1 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 2)]
    linarith [(by norm_num : (1 : ℝ) * (1 + 1 / 2 ^ 51) + 2 / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 2 ^ 800)]
  obtain ⟨a3f, b3f, e3, hb3, ha3⟩ := sumDD_spec a1 b1 l2 0.0 a1f b1f lf zero_finite
    (by linarith [(by norm_num : (1 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 < 2 ^ 898)])
    (by
      have := div_le_div_of_nonneg_right hh2A (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
      linarith [(by norm_num : (2 : ℝ) ^ 11 / 2 ^ 52 + 1 / 2 ^ 1074 < 2 ^ 898)])
    _ hl3 hL3
  generalize sumDD a1 b1 l2 0.0 = S at a3f b3f e3 hb3 ha3
  obtain ⟨a3, b3⟩ := S
  dsimp only at a3f b3f e3 hb3 ha3 ⊢
  rw [zero_value, add_zero] at e3
  refine ⟨hf, a3f, b3f, ?_, hh2, ?_, ?_⟩
  · -- the error
    have key : value h2.toBits + value a3.toBits + value b3.toBits -
        (value fh.toBits + value fl.toBits + value fll.toBits +
          (value lh.toBits + value ll.toBits + value lll.toBits)) =
        (value a3.toBits + value b3.toBits - (value a1.toBits + value b1.toBits + value l2.toBits)) +
          (value a1.toBits + value b1.toBits -
            (value fl.toBits + value fll.toBits + (value ll.toBits + value lll.toBits))) := by
      linarith
    rw [key]
    have h1 := abs_add_le (value a3.toBits + value b3.toBits -
      (value a1.toBits + value b1.toBits + value l2.toBits))
      (value a1.toBits + value b1.toBits -
        (value fl.toBits + value fll.toBits + (value ll.toBits + value lll.toBits)))
    have ha3' : |value a3.toBits| ≤ (B * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 +
        (|value h2.toBits| / 2 ^ 52 + 1 / 2 ^ 1074)) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 := by
      have := abs_add_le (value a1.toBits) (value l2.toBits)
      have := mul_le_mul_of_nonneg_right (this.trans (add_le_add ha1' hlo))
        (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
      linarith
    have hB1 : |value a1.toBits| / 2 ^ 51 ≤ B / 2 ^ 50 + 1 / 2 ^ 1100 := by
      have := div_le_div_of_nonneg_right ha1' (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 * (1 + 1 / 2 ^ 51) ≤ 1 / 2 ^ 50),
        (by norm_num : (1 : ℝ) / 2 ^ 1073 / 2 ^ 51 ≤ 1 / 2 ^ 1101), mul_le_mul_of_nonneg_left
          (by norm_num : (1 : ℝ) / 2 ^ 51 * (1 + 1 / 2 ^ 51) ≤ 1 / 2 ^ 50) hB0]
    have hA3 : |value a3.toBits| / 2 ^ 52 ≤ B / 2 ^ 51 + |value h2.toBits| / 2 ^ 103 +
        1 / 2 ^ 1100 := by
      have := div_le_div_of_nonneg_right ha3' (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
      have hh0 := abs_nonneg (value h2.toBits)
      linarith
    linarith [abs_nonneg (value h2.toBits)]
  · -- the middle part
    have := abs_add_le (value a1.toBits) (value l2.toBits)
    have := mul_le_mul_of_nonneg_right (this.trans (add_le_add ha1' hlo))
      (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    linarith [abs_nonneg (value h2.toBits)]
  · -- the low part
    have hB1 : |value a1.toBits| / 2 ^ 51 ≤ B / 2 ^ 50 + 1 / 2 ^ 1100 := by
      have := div_le_div_of_nonneg_right ha1' (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
      linarith
    linarith [abs_nonneg (value a3.toBits)]

#print axioms addLog_spec

end Verified.Examples.LgammaAccAdd
