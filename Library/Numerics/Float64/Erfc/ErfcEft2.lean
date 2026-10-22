import Library.Numerics.Float64.Erfc.ErfcEft
import LeanExe.ProofKit.F64NegateOps
import LeanExe.ProofKit.F64MulBounds
import LeanExe.ProofKit.F64NearestHalf
import LeanExe.ProofKit.F64Sign

/-!
Knuth's `TwoSum` for the proof of `Erfc.erfc`: `two_sum` shows that it returns `s + t = a + b`
exactly.  For `|a| ≤ |b|` its first steps are `Fast2Sum (b, a)`.  For `|b| ≤ |a|` and `|s| < |b|`
the sum is exact by Sterbenz's lemma.  For `|b| ≤ |s|`, `Fast2Sum (a, b)` gives the error of `s`,
`Fast2Sum (s, -b)` the error of `aa = s - b` and the exactness of `s - aa`, and a grid argument the
exactness of `a - aa`, which lies within twice the error of `s` of zero.
-/

namespace Library.Numerics.Float64.Erfc.ErfcEft2

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft

set_option exponentiation.threshold 2200

/-- `Erfc.twoSum` on words. -/
def twoSumW (a b : UInt64) : UInt64 × UInt64 :=
  let s := Wasm.IEEE64.add a b
  let aa := Wasm.IEEE64.sub s b
  let bb := Wasm.IEEE64.sub s aa
  (s, Wasm.IEEE64.add (Wasm.IEEE64.sub a aa) (Wasm.IEEE64.sub b bb))

theorem rep_zero : Rep 0 := by
  have := rep_grid 0 0 (by norm_num) (by norm_num)
  simpa using this

theorem rep_abs (w : UInt64) (hw : Finite w) : Rep |value w| := by
  rcases le_total 0 (value w) with h | h
  · rw [abs_of_nonneg h]; exact rep_word w hw
  · rw [abs_of_nonpos h]; exact rep_neg (rep_word w hw)

theorem abs_sub_le' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  have := abs_add_le x (-y)
  rwa [abs_neg, ← sub_eq_add_neg] at this

/-- The error of a rounded sum against the grid of its larger operand. -/
theorem err_grid (a b : UInt64) (ha : Finite a) (hb : Finite b) (hab : |value b| ≤ |value a|)
    (hbig : |value a| ≤ 2 ^ 1020) :
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ 2 ^ gx a / 2 ^ 1074 := by
  have hga := gx_small a (by linarith [show (2 : ℝ) ^ 1020 < 2 ^ 1021 by norm_num])
  have hlt : |value a + value b| < 2 ^ (53 + (gx a + 1)) / 2 ^ 1074 := by
    have := word_lt a
    have h2 := abs_add_le (value a) (value b)
    rw [show 53 + (gx a + 1) = (53 + gx a) + 1 by ring, pow_succ]
    linarith [show 2 * (2 : ℝ) ^ (53 + gx a) / 2 ^ 1074 = 2 ^ (53 + gx a) * 2 / 2 ^ 1074 by ring]
  have h := (F64NearestSum.add_half_spacing a b ha hb (gx a + 1) hlt (by omega)).2
  rwa [pow_succ, mul_div_cancel_right₀ _ (by norm_num)] at h

/-- Knuth's `TwoSum` is exact. -/
theorem two_sum (a b : UInt64) (ha : Finite a) (hb : Finite b) (hba : |value a| ≤ 2 ^ 1018)
    (hbb : |value b| ≤ 2 ^ 1018) :
    Finite (twoSumW a b).1 ∧ Finite (twoSumW a b).2 ∧
      value (twoSumW a b).1 + value (twoSumW a b).2 = value a + value b ∧
      |value a + value b - value (twoSumW a b).1| ≤ |value b| ∧
      |value a + value b - value (twoSumW a b).1| ≤ |value a| := by
  unfold twoSumW
  dsimp only
  have h18 : (2 : ℝ) ^ 1018 ≤ 2 ^ 1020 := by norm_num
  have h20 : (2 : ℝ) ^ 1020 ≤ 2 ^ 1022 := by norm_num
  set s := Wasm.IEEE64.add a b with hsdef
  rcases le_total |value a| |value b| with hab | hab
  · -- `Fast2Sum (b, a)`.
    have hsc : s = Wasm.IEEE64.add b a := F64NegateOps.add_comm a b
    obtain ⟨hsf, hzf, hzv, htf, htv, he⟩ := fast_two_sum b a hb ha hab (by linarith)
    rw [← hsc] at hsf hzf hzv htf htv he
    rw [add_comm (value b)] at htv he
    have hbbv : value s - value (Wasm.IEEE64.sub s b) = value b := by rw [hzv]; ring
    obtain ⟨hbbf, hbbv'⟩ := sub_exact_rep s _ hsf hzf
      (by rw [hbbv]; linarith) (by rw [hbbv]; exact rep_word b hb)
    rw [hbbv] at hbbv'
    obtain ⟨hdbf, hdbv⟩ := sub_exact_rep b _ hb hbbf
      (by rw [hbbv', sub_self, abs_zero]; positivity) (by rw [hbbv', sub_self]; exact rep_zero)
    rw [hbbv', sub_self] at hdbv
    have hda := abs_nonneg (value a)
    obtain ⟨hdf, hdv⟩ := add_exact_rep _ _ htf hdbf
      (by rw [hdbv, add_zero, htv]; linarith) (by rw [hdbv, add_zero]; exact rep_word _ htf)
    refine ⟨hsf, hdf, by rw [hdv, hdbv, add_zero, htv]; ring, by linarith, he⟩
  · obtain ⟨hsf, hn⟩ := add_near a b ha hb (by
      have := abs_add_le (value a) (value b); linarith)
    rcases le_or_gt |value b| |value s| with hbs | hbs
    · -- `Fast2Sum (a, b)` and `Fast2Sum (s, -b)`.
      obtain ⟨-, -, -, htf, htv, he⟩ := fast_two_sum a b ha hb hab (by linarith)
      have hre : Rep (value a + value b - value s) := by rw [← htv]; exact rep_word _ htf
      obtain ⟨hnb, hnbv⟩ := F64Magnitude.negate_value b hb
      have hsb : |value s| ≤ 3 * 2 ^ 1018 := by
        have h1 := abs_sub_abs_le_abs_sub (value s) (value a + value b)
        have h2 := abs_add_le (value a) (value b)
        rw [abs_sub_comm] at he
        linarith
      obtain ⟨haaf, hzf2, hzv2, htf2, htv2, he2⟩ := fast_two_sum s (Wasm.IEEE64.negate b) hsf hnb
        (by rw [hnbv, abs_neg]; exact hbs)
        (by linarith [show (3 : ℝ) * 2 ^ 1018 ≤ 2 ^ 1020 by norm_num])
      have hsub : Wasm.IEEE64.add s (Wasm.IEEE64.negate b) = Wasm.IEEE64.sub s b := rfl
      rw [hsub] at haaf hzf2 hzv2 htf2 htv2 he2
      rw [hnbv, ← sub_eq_add_neg] at htv2
      rw [hnbv, abs_neg, ← sub_eq_add_neg] at he2
      set aa := Wasm.IEEE64.sub s b with haadef
      have hsb2 : |value s - value b| ≤ 2 ^ 1022 := by
        have := abs_sub_le' (value s) (value b)
        linarith [show (4 : ℝ) * 2 ^ 1018 ≤ 2 ^ 1022 by norm_num]
      -- `bb = s - aa` is exact.
      have hbbr : Rep (value s - value aa) := by
        have := rep_neg (rep_word _ hzf2)
        rwa [hzv2, neg_sub] at this
      have hsaa : |value s - value aa| ≤ 2 * |value b| := by
        have := abs_add_le (value s - value b - value aa) (value b)
        rw [show value s - value b - value aa + value b = value s - value aa by ring] at this
        linarith
      obtain ⟨hbbf, hbbv⟩ := sub_exact_rep s aa hsf haaf (by linarith) hbbr
      -- `a - aa` is exact: it lies within twice the error of `s` on the grid of `a`.
      have hnear := (sub_near s b hsf hb hsb2).2 a
      rw [show value a - (value s - value b) = value a + value b - value s by ring] at hnear
      have heg := err_grid a b ha hb hab (by linarith)
      rw [abs_sub_comm] at heg
      have hdaa : |value a - value aa| ≤ 2 * (2 ^ gx a / 2 ^ 1074) := by
        have h1 := abs_add_le (value a + value b - value s) (value s - value b - value aa)
        rw [show value a + value b - value s + (value s - value b - value aa) =
          value a - value aa by ring, abs_sub_comm (value s - value b)] at h1
        linarith
      have hga := gx_small a (by linarith [show (2 : ℝ) ^ 1018 < 2 ^ 1021 by norm_num])
      have hgaa : gx a - 1 ≤ gx aa := by
        by_cases hae : 1 ≤ Wasm.IEEE64.exponent a
        · by_cases hg0 : gx a = 0
          · omega
          · apply gx_ge
            have hA := word_ge a hae
            have h1 := abs_sub_abs_le_abs_sub (value a) (value aa)
            have h2 : (2 : ℝ) ^ (52 + (gx a - 1)) * 2 = 2 ^ (52 + gx a) := by
              rw [← pow_succ]; congr 1; omega
            have h3 : (2 : ℝ) ^ gx a * 4 ≤ 2 ^ (52 + gx a) / 2 := by
              rw [pow_add]
              have : (0 : ℝ) < 2 ^ gx a := by positivity
              nlinarith [show (4 : ℝ) ≤ 2 ^ 52 / 2 by norm_num]
            have h4 : 2 * (2 ^ gx a / 2 ^ 1074) ≤ (2 : ℝ) ^ (52 + gx a) / 2 / 2 ^ 1074 := by
              have := div_le_div_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
              have hp : (0 : ℝ) ≤ 2 ^ gx a / 2 ^ 1074 := by positivity
              have e : (2 : ℝ) ^ gx a * 4 / 2 ^ 1074 = 4 * (2 ^ gx a / 2 ^ 1074) := by ring
              linarith
            have h5 : (2 : ℝ) ^ (52 + (gx a - 1)) / 2 ^ 1074 = 2 ^ (52 + gx a) / 2 / 2 ^ 1074 := by
              rw [← h2]; ring
            have h6 : (2 : ℝ) ^ (52 + gx a) / 2 / 2 ^ 1074 = 2 ^ (52 + gx a) / 2 ^ 1074 / 2 := by
              ring
            linarith
        · have : gx a = 0 := by unfold gx; omega
          omega
      have hdar : Rep (value a - value aa) := by
        have hgo : OnGrid (value a - value aa) (min (gx a) (gx aa)) :=
          onGrid_sub (onGrid_mono (onGrid_word a) (min_le_left _ _))
            (onGrid_mono (onGrid_word aa) (min_le_right _ _))
        refine rep_of_onGrid hgo (by omega) ?_
        have hk : gx a ≤ min (gx a) (gx aa) + 1 := by omega
        have h1 : (2 : ℝ) ^ gx a ≤ 2 ^ (min (gx a) (gx aa) + 1) :=
          pow_le_pow_right₀ (by norm_num) hk
        rw [pow_succ] at h1
        have h2 : (2 : ℝ) * (2 ^ gx a / 2 ^ 1074) ≤
            4 * (2 ^ min (gx a) (gx aa) / 2 ^ 1074) := by
          have := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
          linarith [show 2 ^ min (gx a) (gx aa) * 2 / (2 : ℝ) ^ 1074 =
            2 * (2 ^ min (gx a) (gx aa) / 2 ^ 1074) by ring]
        have h3 : (0 : ℝ) < 2 ^ min (gx a) (gx aa) / 2 ^ 1074 := by positivity
        rw [show (2 ^ 53 + 1 : ℝ) * 2 ^ min (gx a) (gx aa) / 2 ^ 1074 =
          (2 ^ 53 + 1) * (2 ^ min (gx a) (gx aa) / 2 ^ 1074) by ring]
        nlinarith
      obtain ⟨hdaf, hdav⟩ := sub_exact_rep a aa ha haaf (by
        have h3 : (2 : ℝ) ^ gx a ≤ 2 ^ 2042 := pow_le_pow_right₀ (by norm_num) hga
        have h4 := div_le_div_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 ^ 1074)
        linarith [show (2 : ℝ) * (2 ^ 2042 / 2 ^ 1074) ≤ 2 ^ 1022 by norm_num]) hdar
      -- `b - bb` is the error of `aa`.
      have hbbv2 : value b - value (Wasm.IEEE64.sub s aa) = -(value s - value b - value aa) := by
        rw [hbbv]; ring
      obtain ⟨hdbf, hdbv⟩ := sub_exact_rep b _ hb hbbf
        (by rw [hbbv2, abs_neg]; linarith)
        (by rw [hbbv2, ← htv2]; exact rep_neg (rep_word _ htf2))
      -- The final sum is the error of `s`.
      have hsum : value (Wasm.IEEE64.sub a aa) + value (Wasm.IEEE64.sub b (Wasm.IEEE64.sub s aa)) =
          value a + value b - value s := by
        rw [hdav, hdbv, hbbv2]; ring
      obtain ⟨htf3, htv3⟩ := add_exact_rep _ _ hdaf hdbf
        (by rw [hsum]; linarith) (by rw [hsum]; exact hre)
      refine ⟨hsf, htf3, by rw [htv3, hsum]; ring, he, by linarith⟩
    · -- `|s| < |b|`: the sum is exact by Sterbenz's lemma.
      have ht : |value a + value b| ≤ |value b| := by
        by_contra hc
        push Not at hc
        have := nearest_ge s _ _ hn (rep_abs b hb) (abs_nonneg _) hc.le
        linarith
      obtain ⟨hnb, hnbv⟩ := F64Magnitude.negate_value b hb
      obtain ⟨-, hsv⟩ := F64Sterbenz.sub_exact a (Wasm.IEEE64.negate b) ha hnb
        (by rw [hnbv, sub_neg_eq_add]; linarith)
        (by rw [hnbv, sub_neg_eq_add, abs_neg]; exact ht)
        (by rw [hnbv, abs_neg]; linarith [show (2 : ℝ) ^ 1018 < 2 ^ 1021 by norm_num])
      rw [← add_eq_sub, hnbv, sub_neg_eq_add] at hsv
      -- Every later step is exact.
      obtain ⟨haaf, haav⟩ := sub_exact_rep s b hsf hb
        (by rw [hsv, add_sub_cancel_right]; linarith) (by rw [hsv, add_sub_cancel_right]; exact rep_word a ha)
      rw [hsv, add_sub_cancel_right] at haav
      obtain ⟨hbbf, hbbv⟩ := sub_exact_rep s _ hsf haaf
        (by rw [hsv, haav, add_sub_cancel_left]; linarith)
        (by rw [hsv, haav, add_sub_cancel_left]; exact rep_word b hb)
      rw [hsv, haav, add_sub_cancel_left] at hbbv
      obtain ⟨hdaf, hdav⟩ := sub_exact_rep a _ ha haaf
        (by rw [haav, sub_self, abs_zero]; positivity) (by rw [haav, sub_self]; exact rep_zero)
      rw [haav, sub_self] at hdav
      obtain ⟨hdbf, hdbv⟩ := sub_exact_rep b _ hb hbbf
        (by rw [hbbv, sub_self, abs_zero]; positivity) (by rw [hbbv, sub_self]; exact rep_zero)
      rw [hbbv, sub_self] at hdbv
      obtain ⟨htf, htv⟩ := add_exact_rep _ _ hdaf hdbf
        (by rw [hdav, hdbv, add_zero, abs_zero]; positivity)
        (by rw [hdav, hdbv, add_zero]; exact rep_zero)
      refine ⟨hsf, htf, by rw [htv, hdav, hdbv, hsv]; ring, ?_, ?_⟩ <;>
        rw [hsv, sub_self, abs_zero] <;> positivity

#print axioms two_sum

end Library.Numerics.Float64.Erfc.ErfcEft2
