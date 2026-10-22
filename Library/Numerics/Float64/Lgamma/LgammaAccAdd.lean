import Library.Numerics.Float64.Lgamma.LgammaAccLow

/-!
The addition of a logarithm `lh + ll + lll` to a triple `fh + fl + fll` in the windows of
`Lgamma.accurate` from `1/4` to `15/4`: `sumDD` of the low parts, `twoSum` of the high parts, and
`sumDD` of the new low part with the low part of the `twoSum`.  The `twoSum` is exact, and each
`sumDD` adds about `2^-53` of its low parts and `2^-105` of its high part (`addLog_spec`), so the
error stays near `2^-53` of the low parts and `2^-150` of the high part.  The theorem takes the
three intermediate pairs as variables with their equations, the form in which
`LgammaWalk.walk_step` leaves the code.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccAdd
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD

set_option exponentiation.threshold 4096

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
theorem addLog_gen (fh fl fll lh ll lll : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (hfll : Finite fll.toBits) (hlh : Finite lh.toBits)
    (hll : Finite ll.toBits) (hlll : Finite lll.toBits) (A B L1 : ℝ)
    (hA : |value fh.toBits| + |value lh.toBits| ≤ A) (hA' : A ≤ 2 ^ 850)
    (hB : |value fl.toBits| + |value ll.toBits| ≤ B) (hB' : B ≤ 2 ^ 840)
    (hL : |value fll.toBits| + |value lll.toBits| ≤ L1) (hL' : L1 ≤ 2 ^ 790)
    (a1 b1 : Float) (hS1 : sumDD fl fll ll lll = (a1, b1))
    (h2 l2 : Float) (hf : Finite h2.toBits) (lf : Finite l2.toBits)
    (hsum : value h2.toBits + value l2.toBits = value fh.toBits + value lh.toBits)
    (hlo : |value l2.toBits| ≤ |value h2.toBits| / 2 ^ 52 + 1 / 2 ^ 1074)
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    Finite h2.toBits ∧ Finite a3.toBits ∧ Finite b3.toBits ∧
      |value h2.toBits + value a3.toBits + value b3.toBits -
          (value fh.toBits + value fl.toBits + value fll.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits))| ≤
        (7 * L1 + B / 2 ^ 47 + |value h2.toBits| / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100 ∧
      |value h2.toBits| ≤ |value fh.toBits + value lh.toBits| * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ∧
      |value a3.toBits| ≤ (B + |value h2.toBits| / 2 ^ 52) * (1 + 1 / 2 ^ 49) + 1 / 2 ^ 1070 ∧
      |value b3.toBits| ≤ (L1 + B / 2 ^ 50) * (1 + 1 / 2 ^ 49) + |value a3.toBits| / 2 ^ 51 +
        1 / 2 ^ 1070 := by
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  have hL0 : 0 ≤ L1 := le_trans (by positivity) hL
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  -- `sumDD fl fll ll lll`
  have hl1 : |value fll.toBits| + |value lll.toBits| ≤ L1 := hL
  obtain ⟨a1f, b1f, e1, hb1, ha1⟩ := sumDD_spec fl fll ll lll hfl hfll hll hlll
    (by linarith [abs_nonneg (value ll.toBits), (by norm_num : (2 : ℝ) ^ 840 < 2 ^ 898)])
    (by linarith [abs_nonneg (value fl.toBits), (by norm_num : (2 : ℝ) ^ 840 < 2 ^ 898)])
    L1 hl1 (by linarith [(by norm_num : (2 : ℝ) ^ 790 ≤ 2 ^ 800)])
  rw [hS1] at a1f b1f e1 hb1 ha1
  dsimp only at a1f b1f e1 hb1 ha1
  have ha1' : |value a1.toBits| ≤ B * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 := by
    have := abs_add_le (value fl.toBits) (value ll.toBits)
    have := mul_le_mul_of_nonneg_right (this.trans hB) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    linarith
  -- the exact sum of the high parts
  have hh2 : |value h2.toBits| ≤ |value fh.toBits + value lh.toBits| * (1 + 1 / 2 ^ 51) +
      1 / 2 ^ 1073 := high_bound h2 l2 _ hsum hlo
  have hh2A : |value h2.toBits| ≤ 2 ^ 851 := by
    have := abs_add_le (value fh.toBits) (value lh.toBits)
    have := mul_le_mul_of_nonneg_right (this.trans (hA.trans hA'))
      (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    linarith [(by norm_num : (2 : ℝ) ^ 850 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 2 ^ 851)]
  -- `sumDD a1 b1 l2 0`
  have hl3 : |value b1.toBits| + |value (0.0 : Float).toBits| ≤
      L1 * (1 + 1 / 2 ^ 51) + |value a1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 := by
    rw [zero_value, abs_zero, add_zero]; exact hb1
  have hL3 : L1 * (1 + 1 / 2 ^ 51) + |value a1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 ≤ 2 ^ 800 := by
    have : |value a1.toBits| ≤ 2 ^ 841 := by
      nlinarith [(by norm_num : (2 : ℝ) ^ 840 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 2 ^ 841)]
    have h2 := mul_le_mul_of_nonneg_right hL' (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    have h3 := div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    linarith [(by norm_num : (2 : ℝ) ^ 790 * (1 + 1 / 2 ^ 51) + 2 ^ 841 / 2 ^ 51 + 1 / 2 ^ 1073 ≤
      2 ^ 800)]
  obtain ⟨a3f, b3f, e3, hb3, ha3⟩ := sumDD_spec a1 b1 l2 0.0 a1f b1f lf zero_finite
    (by nlinarith [(by norm_num : (2 : ℝ) ^ 840 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 < 2 ^ 898)])
    (by
      have := div_le_div_of_nonneg_right hh2A (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
      linarith [(by norm_num : (2 : ℝ) ^ 851 / 2 ^ 52 + 1 / 2 ^ 1074 < 2 ^ 898)])
    _ hl3 hL3
  rw [hS3] at a3f b3f e3 hb3 ha3
  dsimp only at a3f b3f e3 hb3 ha3
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

/-- **`addLog`** with `twoSum` for the high parts. -/
theorem addLog_spec (fh fl fll lh ll lll : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (hfll : Finite fll.toBits) (hlh : Finite lh.toBits)
    (hll : Finite ll.toBits) (hlll : Finite lll.toBits) (A B L1 : ℝ)
    (hA : |value fh.toBits| + |value lh.toBits| ≤ A) (hA' : A ≤ 2 ^ 10)
    (hB : |value fl.toBits| + |value ll.toBits| ≤ B) (hB' : B ≤ 1)
    (hL : |value fll.toBits| + |value lll.toBits| ≤ L1) (hL' : L1 ≤ 1)
    (a1 b1 : Float) (hS1 : sumDD fl fll ll lll = (a1, b1))
    (h2 l2 : Float) (hP2 : twoSum fh lh = (h2, l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    Finite h2.toBits ∧ Finite a3.toBits ∧ Finite b3.toBits ∧
      |value h2.toBits + value a3.toBits + value b3.toBits -
          (value fh.toBits + value fl.toBits + value fll.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits))| ≤
        (7 * L1 + B / 2 ^ 47 + |value h2.toBits| / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100 ∧
      |value h2.toBits| ≤ |value fh.toBits + value lh.toBits| * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ∧
      |value a3.toBits| ≤ (B + |value h2.toBits| / 2 ^ 52) * (1 + 1 / 2 ^ 49) + 1 / 2 ^ 1070 ∧
      |value b3.toBits| ≤ (L1 + B / 2 ^ 50) * (1 + 1 / 2 ^ 49) + |value a3.toBits| / 2 ^ 51 +
        1 / 2 ^ 1070 := by
  obtain ⟨hf, lf, hsum, hlo⟩ := twoSum_spec fh lh hfh hlh
    (by linarith [abs_nonneg (value lh.toBits), (by norm_num : (2 : ℝ) ^ 10 < 2 ^ 900)])
    (by linarith [abs_nonneg (value fh.toBits), (by norm_num : (2 : ℝ) ^ 10 < 2 ^ 900)])
  rw [hP2] at hf lf hsum hlo
  exact addLog_gen fh fl fll lh ll lll hfh hfl hfll hlh hll hlll A B L1 hA (hA'.trans (by norm_num))
    hB (hB'.trans (by norm_num)) hL (hL'.trans (by norm_num)) a1 b1
    hS1 h2 l2 hf lf hsum hlo a3 b3 hS3

/-- **`addLog`** with `fastTwoSum` for the high parts, for `|lh| ≤ |fh|`. -/
theorem addLog_fast (fh fl fll lh ll lll : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (hfll : Finite fll.toBits) (hlh : Finite lh.toBits)
    (hll : Finite ll.toBits) (hlll : Finite lll.toBits) (A B L1 : ℝ)
    (hord : |value lh.toBits| ≤ |value fh.toBits|)
    (hA : |value fh.toBits| + |value lh.toBits| ≤ A) (hA' : A ≤ 2 ^ 10)
    (hB : |value fl.toBits| + |value ll.toBits| ≤ B) (hB' : B ≤ 1)
    (hL : |value fll.toBits| + |value lll.toBits| ≤ L1) (hL' : L1 ≤ 1)
    (a1 b1 : Float) (hS1 : sumDD fl fll ll lll = (a1, b1))
    (h2 l2 : Float) (hP2 : fastTwoSum fh lh = (h2, l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    Finite h2.toBits ∧ Finite a3.toBits ∧ Finite b3.toBits ∧
      |value h2.toBits + value a3.toBits + value b3.toBits -
          (value fh.toBits + value fl.toBits + value fll.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits))| ≤
        (7 * L1 + B / 2 ^ 47 + |value h2.toBits| / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100 ∧
      |value h2.toBits| ≤ |value fh.toBits + value lh.toBits| * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ∧
      |value a3.toBits| ≤ (B + |value h2.toBits| / 2 ^ 52) * (1 + 1 / 2 ^ 49) + 1 / 2 ^ 1070 ∧
      |value b3.toBits| ≤ (L1 + B / 2 ^ 50) * (1 + 1 / 2 ^ 49) + |value a3.toBits| / 2 ^ 51 +
        1 / 2 ^ 1070 := by
  obtain ⟨hf, lf, hsum, -, hlo⟩ := fastTwoSum_spec fh lh hfh hlh hord
    (by linarith [abs_nonneg (value lh.toBits), (by norm_num : (2 : ℝ) ^ 10 < 2 ^ 900)])
  rw [hP2] at hf lf hsum hlo
  exact addLog_gen fh fl fll lh ll lll hfh hfl hfll hlh hll hlll A B L1 hA (hA'.trans (by norm_num))
    hB (hB'.trans (by norm_num)) hL (hL'.trans (by norm_num)) a1 b1
    hS1 h2 l2 hf lf hsum hlo a3 b3 hS3

/-- **`addLog`** with `twoSum`, for high parts up to `2^850`. -/
theorem addLog_wide (fh fl fll lh ll lll : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (hfll : Finite fll.toBits) (hlh : Finite lh.toBits)
    (hll : Finite ll.toBits) (hlll : Finite lll.toBits) (A B L1 : ℝ)
    (hA : |value fh.toBits| + |value lh.toBits| ≤ A) (hA' : A ≤ 2 ^ 850)
    (hB : |value fl.toBits| + |value ll.toBits| ≤ B) (hB' : B ≤ 2 ^ 840)
    (hL : |value fll.toBits| + |value lll.toBits| ≤ L1) (hL' : L1 ≤ 2 ^ 790)
    (a1 b1 : Float) (hS1 : sumDD fl fll ll lll = (a1, b1))
    (h2 l2 : Float) (hP2 : twoSum fh lh = (h2, l2))
    (a3 b3 : Float) (hS3 : sumDD a1 b1 l2 0.0 = (a3, b3)) :
    Finite h2.toBits ∧ Finite a3.toBits ∧ Finite b3.toBits ∧
      |value h2.toBits + value a3.toBits + value b3.toBits -
          (value fh.toBits + value fl.toBits + value fll.toBits +
            (value lh.toBits + value ll.toBits + value lll.toBits))| ≤
        (7 * L1 + B / 2 ^ 47 + |value h2.toBits| / 2 ^ 100) / 2 ^ 53 + 1 / 2 ^ 1100 ∧
      |value h2.toBits| ≤ |value fh.toBits + value lh.toBits| * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ∧
      |value a3.toBits| ≤ (B + |value h2.toBits| / 2 ^ 52) * (1 + 1 / 2 ^ 49) + 1 / 2 ^ 1070 ∧
      |value b3.toBits| ≤ (L1 + B / 2 ^ 50) * (1 + 1 / 2 ^ 49) + |value a3.toBits| / 2 ^ 51 +
        1 / 2 ^ 1070 := by
  obtain ⟨hf, lf, hsum, hlo⟩ := twoSum_spec fh lh hfh hlh
    (by linarith [abs_nonneg (value lh.toBits), (by norm_num : (2 : ℝ) ^ 850 < 2 ^ 900)])
    (by linarith [abs_nonneg (value fh.toBits), (by norm_num : (2 : ℝ) ^ 850 < 2 ^ 900)])
  rw [hP2] at hf lf hsum hlo
  exact addLog_gen fh fl fll lh ll lll hfh hfl hfll hlh hll hlll A B L1 hA hA' hB hB' hL hL' a1 b1
    hS1 h2 l2 hf lf hsum hlo a3 b3 hS3

#print axioms addLog_gen
#print axioms addLog_wide
#print axioms addLog_spec
#print axioms addLog_fast

end Library.Numerics.Float64.Lgamma.LgammaAccAdd
