import Verified.Examples.ErfcEft2
import Verified.Examples.Erfc
import LeanExe.ProofKit.F64Bits

/-!
The operations of `Erfc` on floats with their error bounds, for the proof of `Erfc.erfc`.  `fv x`
is the value of a float's bits.  Sums and differences err by at most `u` relative, products by
`u` relative plus `2 ^ -1075`, and `Fma.fma` by the same under `FmaSpec.FmaNearest`.
`Erfc.fastTwoSum` and `Erfc.twoSum` are exact, and `Erfc.aMul` errs by at most `2 ^ -106` relative
plus `2 ^ -1074`.
-/

namespace Verified.Examples.ErfcOps

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft ErfcEft2 FmaSpec

set_option exponentiation.threshold 2200

/-- The value of a float. -/
noncomputable def fv (x : Float) : ℝ := value x.toBits

/-- A finite float. -/
def ff (x : Float) : Prop := Finite x.toBits

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

theorem neg_f (x : Float) (hx : ff x) : ff (-x) ∧ fv (-x) = -fv x := by
  unfold ff fv at *
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, ite_eq_right (by rw [not_nan_of_finite hx]; decide)]
  exact F64Magnitude.negate_value _ hx

theorem add_f (a b : Float) (ha : ff a) (hb : ff b) (h : |fv a + fv b| ≤ 2 ^ 1022) :
    ff (a + b) ∧ |fv (a + b) - (fv a + fv b)| ≤ u * |fv a + fv b| := by
  unfold ff fv at *
  rw [F64Bits.toBits_add]
  exact F64AddBounds.add_real_relative _ _ ha hb (lt_of_le_of_lt h (by norm_num))

theorem sub_f (a b : Float) (ha : ff a) (hb : ff b) (h : |fv a - fv b| ≤ 2 ^ 1022) :
    ff (a - b) ∧ |fv (a - b) - (fv a - fv b)| ≤ u * |fv a - fv b| := by
  unfold ff fv at *
  rw [F64Bits.toBits_sub]
  exact F64AddBounds.sub_real_relative _ _ ha hb (lt_of_le_of_lt h (by norm_num))

theorem mul_f (a b : Float) (ha : ff a) (hb : ff b) (h : |fv a * fv b| ≤ 2 ^ 1021) :
    ff (a * b) ∧ |fv (a * b) - fv a * fv b| ≤ u * |fv a * fv b| + η := by
  unfold ff fv at *
  rw [F64Bits.toBits_mul]
  obtain ⟨hf, he⟩ := F64MulBounds.mul_real_adaptive _ _ ha hb (lt_of_le_of_lt h (by norm_num))
  refine ⟨hf, le_trans he ?_⟩
  dsimp only
  have hm : minNormal64 = 1 / 2 ^ 1022 := rfl
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  rw [hu]
  split
  · rw [mul_zero]; positivity
  · rw [hm]
    have h1 : max |value a.toBits * value b.toBits| (1 / 2 ^ 1022) ≤
        |value a.toBits * value b.toBits| + 1 / 2 ^ 1022 :=
      max_le (by linarith [show (0 : ℝ) ≤ 1 / 2 ^ 1022 by positivity])
        (by linarith [abs_nonneg (value a.toBits * value b.toBits)])
    have h2 : (1 : ℝ) / 2 ^ 53 * (1 / 2 ^ 1022) = 1 / 2 ^ 1075 := by norm_num
    nlinarith [show (0 : ℝ) ≤ 1 / 2 ^ 53 by positivity]

/-- A nearest float to `t` is within `u |t| + 2 ^ -1075` of it. -/
theorem nearest_err (c : UInt64) (t : ℝ) (hn : ∀ v : UInt64, Finite v → |value c - t| ≤ |value v - t|)
    (ht : |t| < 2 ^ 1022) : |value c - t| ≤ u * |t| + η := by
  obtain ⟨w, hw⟩ := F64NearestNonnegative.exists_nearest |t|
  obtain ⟨hwf, -⟩ := F64NearestNonnegative.nearest_finite _ _ hw
  have hwt : |(value w - |t|)| ≤ u * |t| + η := by
    rcases le_or_gt (1 / 2 ^ 1022) |t| with hbig | hsmall
    · have := F64NearestHalf.nearest_relative |t| w hw hbig ht
      rw [show unitRoundoff64 = 1 / 2 ^ 53 from rfl] at this
      linarith [show (0 : ℝ) ≤ η by positivity]
    · have := F64NearestHalf.nearest_half |t| w hw (abs_nonneg _) 0 (by norm_num)
        (by rw [show (53 + 0 : ℕ) = 53 from rfl]
            linarith [show (1 : ℝ) / 2 ^ 1022 ≤ 2 ^ 53 / 2 ^ 1074 by norm_num])
      rw [pow_zero] at this
      have : (1 : ℝ) / 2 / 2 ^ 1074 = η := by norm_num
      nlinarith [abs_nonneg t, show (0 : ℝ) ≤ u by positivity]
  rcases le_total 0 t with h0 | h0
  · have := hn w hwf
    rw [abs_of_nonneg h0] at hwt
    rw [abs_of_nonneg h0]
    linarith
  · obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value w hwf
    have := hn _ hnf
    rw [hnv, show -value w - t = -(value w - -t) by ring, abs_neg] at this
    rw [abs_of_nonpos h0] at hwt ⊢
    linarith

/-- The error of `Fma.fma` under `FmaNearest`. -/
theorem fma_f (hF : FmaNearest) (a b c : Float) (ha : ff a) (hb : ff b) (hc : ff c)
    (h : |fv a * fv b + fv c| ≤ 2 ^ 1021) :
    ff (Fma.fma a b c) ∧ |fv (Fma.fma a b c) - (fv a * fv b + fv c)| ≤
      u * |fv a * fv b + fv c| + η := by
  obtain ⟨hf, hn⟩ := hF a b c ha hb hc (le_trans h (by norm_num))
  exact ⟨hf, nearest_err _ _ hn (lt_of_le_of_lt h (by norm_num))⟩

/-- `Erfc.fastTwoSum` is exact for `|b| ≤ |a|`. -/
theorem fastTwoSum_f (a b : Float) (ha : ff a) (hb : ff b) (hab : |fv b| ≤ |fv a|)
    (hbig : |fv a| ≤ 2 ^ 1020) :
    ff (Erfc.fastTwoSum a b).1 ∧ ff (Erfc.fastTwoSum a b).2 ∧
      fv (Erfc.fastTwoSum a b).1 + fv (Erfc.fastTwoSum a b).2 = fv a + fv b ∧
      |fv a + fv b - fv (Erfc.fastTwoSum a b).1| ≤ |fv b| := by
  unfold Erfc.fastTwoSum ff fv at *
  dsimp only
  simp only [F64Bits.toBits_add, F64Bits.toBits_sub]
  obtain ⟨hsf, -, -, htf, htv, he⟩ := fast_two_sum _ _ ha hb hab hbig
  exact ⟨hsf, htf, by rw [htv]; ring, he⟩

/-- `Erfc.twoSum` is exact. -/
theorem twoSum_f (a b : Float) (ha : ff a) (hb : ff b) (hba : |fv a| ≤ 2 ^ 1018)
    (hbb : |fv b| ≤ 2 ^ 1018) :
    ff (Erfc.twoSum a b).1 ∧ ff (Erfc.twoSum a b).2 ∧
      fv (Erfc.twoSum a b).1 + fv (Erfc.twoSum a b).2 = fv a + fv b ∧
      |fv a + fv b - fv (Erfc.twoSum a b).1| ≤ |fv b| ∧
      |fv a + fv b - fv (Erfc.twoSum a b).1| ≤ |fv a| := by
  have hw : (Erfc.twoSum a b).1.toBits = (twoSumW a.toBits b.toBits).1 ∧
      (Erfc.twoSum a b).2.toBits = (twoSumW a.toBits b.toBits).2 := by
    refine ⟨?_, ?_⟩ <;> simp only [Erfc.twoSum, twoSumW, F64Bits.toBits_add, F64Bits.toBits_sub]
  unfold ff fv at *
  rw [hw.1, hw.2]
  exact two_sum _ _ ha hb hba hbb

/-- `Erfc.aMul`: the product and its error, within `2 ^ -106` relative and `2 ^ -1074`. -/
theorem aMul_f (hF : FmaNearest) (a b : Float) (ha : ff a) (hb : ff b)
    (h : |fv a * fv b| ≤ 2 ^ 1020) :
    ff (Erfc.aMul a b).1 ∧ ff (Erfc.aMul a b).2 ∧
      |fv (Erfc.aMul a b).1 - fv a * fv b| ≤ u * |fv a * fv b| + η ∧
      |fv (Erfc.aMul a b).1 + fv (Erfc.aMul a b).2 - fv a * fv b| ≤
        u * u * |fv a * fv b| + 2 * η := by
  unfold Erfc.aMul
  dsimp only
  obtain ⟨hf1, he1⟩ := mul_f a b ha hb (le_trans h (by norm_num))
  obtain ⟨hnf, hnv⟩ := neg_f (a * b) hf1
  have hsmall : |fv a * fv b + fv (-(a * b))| ≤ u * |fv a * fv b| + η := by
    rw [hnv, show fv a * fv b + -fv (a * b) = -(fv (a * b) - fv a * fv b) by ring, abs_neg]
    exact he1
  have hs2 : |fv a * fv b + fv (-(a * b))| ≤ 2 ^ 1021 := by
    have : u * |fv a * fv b| + η ≤ 2 ^ 1021 := by
      nlinarith [show (1 : ℝ) / 2 ^ 53 * 2 ^ 1020 + 1 / 2 ^ 1075 ≤ 2 ^ 1021 by norm_num,
        abs_nonneg (fv a * fv b)]
    linarith
  obtain ⟨hf2, he2⟩ := fma_f hF a b (-(a * b)) ha hb hnf hs2
  refine ⟨hf1, hf2, he1, ?_⟩
  rw [hnv] at he2
  have e : fv (a * b) + fv (Fma.fma a b (-(a * b))) - fv a * fv b =
      fv (Fma.fma a b (-(a * b))) - (fv a * fv b + -fv (a * b)) := by ring
  rw [e]
  rw [hnv] at hsmall
  calc _ ≤ u * |fv a * fv b + -fv (a * b)| + η := he2
    _ ≤ u * (u * |fv a * fv b| + η) + η := by
        have : (0 : ℝ) ≤ u := by positivity
        nlinarith
    _ ≤ u * u * |fv a * fv b| + 2 * η := by
        have : u * η ≤ η := by
          have : (0 : ℝ) ≤ η := by positivity
          nlinarith [show u ≤ 1 by norm_num]
        nlinarith

#print axioms fma_f
#print axioms fastTwoSum_f
#print axioms twoSum_f
#print axioms aMul_f

end Verified.Examples.ErfcOps
