import Library.Numerics.Float64.Tgamma.TgammaAccFin
import Library.Numerics.Float64.Tgamma.TgammaAccCrr
import Library.Numerics.Float64.Tgamma.TgammaAccBounds

/-!
The end of the accurate path of `Tgamma` from `1/4`, common to its three cases.  The double-double
`f1 + f2` lies within `2 ^ -76` of `Q`, the quotient or product of the computed polynomial and
product, which lies within `ε ≤ 18 · 2 ^ -63` of `Q0`, the same with the exact polynomial and
product, and `Q0` lies within `2 ^ -62` of `g`, `Γ x` scaled by `2 ^ -E`.  `adjLow` moves the low
part by at most `2 ^ -81 |f1|`, so `f1 + fl` lies within `11 · 2 ^ -60` of `g` (`fin_err`), and
`TgammaAccFin.fin_pos` and `fin_neg` round it (`finish_pos`, `finish_neg`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccFinish
open CodeLib.IEEE64 LeanExe.ProofKit TgammaAccFin TgammaAccCrr TgammaAccBounds

set_option exponentiation.threshold 4096

/-- The error of `f1 + fl` from the errors of the steps. -/
theorem fin_err (f1 f2 fl Q Q0 g ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 18 / 2 ^ 63)
    (hS1 : |f1 + f2 - Q| ≤ |Q| / 2 ^ 76) (hQ : |Q - Q0| ≤ ε * |Q0|)
    (hg : |Q0 - g| ≤ |g| / 2 ^ 62) (hf2 : |f2| ≤ |f1| / 2 ^ 30)
    (hfl : |fl - f2| ≤ |f1| / 2 ^ 81) : |f1 + fl - g| ≤ 11 * |g| / 2 ^ 60 := by
  have hf1 : |f1| ≤ 2 * |f1 + f2| := by
    have h := abs_sub_abs_le_abs_sub f1 (-f2)
    rw [abs_neg, sub_neg_eq_add] at h
    have : |f1| / 2 ^ 30 ≤ |f1| / 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
    linarith
  have h1 : |(f1 + fl) - (f1 + f2)| ≤ 1 / 2 ^ 80 * |f1 + f2| := by
    rw [show f1 + fl - (f1 + f2) = fl - f2 by ring]
    have : |f1| / 2 ^ 81 ≤ 2 * |f1 + f2| / 2 ^ 81 :=
      div_le_div_of_nonneg_right hf1 (by positivity)
    linarith [show 2 * |f1 + f2| / 2 ^ 81 = 1 / 2 ^ 80 * |f1 + f2| by ring]
  have h2 : |(f1 + f2) - Q| ≤ 1 / 2 ^ 76 * |Q| := by
    linarith [show |Q| / 2 ^ 76 = 1 / 2 ^ 76 * |Q| by ring]
  have h3 : |Q0 - g| ≤ 1 / 2 ^ 62 * |g| := by
    linarith [show |g| / 2 ^ 62 = 1 / 2 ^ 62 * |g| by ring]
  have c1 := rel_trans _ _ _ _ _ (by norm_num) h1 h2
  have c2 := rel_trans _ _ _ _ _ (by positivity) c1 hQ
  have c3 := rel_trans _ _ _ _ _
    (add_nonneg (add_nonneg (by norm_num) hε0) (mul_nonneg (by norm_num) hε0)) c2 h3
  refine c3.trans ?_
  rw [show 11 * |g| / 2 ^ 60 = 11 / 2 ^ 60 * |g| by ring]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  linarith

/-- `A K` against `Γy K / c` when `c A` lies within `2 ^ -62` of `Γy`. -/
theorem scale_rel (A Γy c K : ℝ) (hc : 0 < c) (hΓ : 0 < Γy) (h : |Γy - c * A| ≤ 1 / 2 ^ 62 * Γy) :
    |A * K - Γy * K / c| ≤ |Γy * K / c| / 2 ^ 62 := by
  have e : A * K - Γy * K / c = (c * A - Γy) * K / c := by
    field_simp
  have hL : |A * K - Γy * K / c| = |Γy - c * A| * |K| / c := by
    rw [e, abs_div, abs_mul, abs_of_pos hc, abs_sub_comm]
  have hR : |Γy * K / c| = Γy * |K| / c := by
    rw [abs_div, abs_mul, abs_of_pos hΓ, abs_of_pos hc]
  rw [hL, hR, div_div, div_le_div_iff₀ hc (mul_pos hc (by positivity))]
  have h1 := mul_le_mul_of_nonneg_right h (abs_nonneg K)
  have h2 := mul_le_mul_of_nonneg_right h1
    (le_of_lt (mul_pos hc (by positivity : (0 : ℝ) < 2 ^ 62)))
  linarith

/-- The size of `f1 + fl` and its parts from the size of `Q0`. -/
theorem fin_sizes (f1 f2 Q Q0 g ε : ℝ) (hε : ε ≤ 18 / 2 ^ 63)
    (hS1 : |f1 + f2 - Q| ≤ |Q| / 2 ^ 76) (hQ : |Q - Q0| ≤ ε * |Q0|)
    (hg : |Q0 - g| ≤ |g| / 2 ^ 62) (hf2 : |f2| ≤ |f1| / 2 ^ 30)
    (hQ1 : 1 / 2 ^ 800 ≤ |Q0|) (hQ2 : |Q0| ≤ 2 ^ 800) :
    1 / 2 ^ 803 ≤ |f1| ∧ |f1| ≤ 2 ^ 803 ∧ 1 / 2 ^ 803 ≤ |g| ∧ |g| ≤ 2 ^ 803 := by
  have a1 := abs_sub_abs_le_abs_sub Q Q0
  have a2 := abs_sub_abs_le_abs_sub Q0 Q
  rw [abs_sub_comm] at a2
  have a3 := abs_sub_abs_le_abs_sub (f1 + f2) Q
  have a4 := abs_sub_abs_le_abs_sub Q (f1 + f2)
  rw [abs_sub_comm] at a4
  have a5 := abs_sub_abs_le_abs_sub g Q0
  rw [abs_sub_comm] at a5
  have a6 := abs_sub_abs_le_abs_sub Q0 g
  have a7 := abs_add_le f1 f2
  have a8 := abs_sub_abs_le_abs_sub f1 (-f2)
  rw [abs_neg, sub_neg_eq_add] at a8
  have hεQ : ε * |Q0| ≤ |Q0| / 2 := by
    have : ε ≤ 1 / 2 := hε.trans (by norm_num)
    nlinarith [abs_nonneg Q0]
  have hQ76 : |Q| / 2 ^ 76 ≤ |Q| / 2 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
    (by norm_num)
  have hg62 : |g| / 2 ^ 62 ≤ |g| / 2 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
    (by norm_num)
  have hf51 : |f1| / 2 ^ 30 ≤ |f1| / 2 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
    (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 803 * 6 ≤ 1 / 2 ^ 800)]
  · linarith [(by norm_num : (2 : ℝ) ^ 800 * 5 ≤ 2 ^ 803)]
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 803 * 2 ≤ 1 / 2 ^ 800)]
  · linarith [(by norm_num : (2 : ℝ) ^ 800 * 2 ≤ 2 ^ 803)]

/-- **The end of the path with a scale `E ≥ 0`.** -/
theorem finish_pos (f1 f2 jm : Float) (E : ℕ) (G Q Q0 ε : ℝ) (hf1 : Finite f1.toBits)
    (hf2 : Finite f2.toBits) (hjm : Finite jm.toBits) (hjmb : |value jm.toBits| ≤ 200)
    (hf2b : |value f2.toBits| ≤ |value f1.toBits| / 2 ^ 30)
    (hS1 : |value f1.toBits + value f2.toBits - Q| ≤ |Q| / 2 ^ 76)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 18 / 2 ^ 63) (hQ : |Q - Q0| ≤ ε * |Q0|)
    (hg : |Q0 - G / 2 ^ E| ≤ |G / 2 ^ E| / 2 ^ 62)
    (hQ1 : 1 / 2 ^ 800 ≤ |Q0|) (hQ2 : |Q0| ≤ 2 ^ 800)
    (hE : E ≤ 1500) (hG2 : |G| ≤ 2 ^ 1024 * (1 - 1 / 2 ^ 50)) :
    F64SignedRounding.WithinSteps 1 G
      (Float.ofBits (finRes f1 (adjLow f1 f2 jm) (UInt64.ofNat E))).toBits := by
  obtain ⟨s1, s2, s3, s4⟩ := fin_sizes _ _ _ _ _ _ hε hS1 hQ hg hf2b hQ1 hQ2
  obtain ⟨hlf, hlb⟩ := adj_low f1 f2 jm hf1 hf2 hjm hjmb
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 900 ≤ 1 / 2 ^ 803)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 803 ≤ 2 ^ 900)]) hf2b
  have herr := fin_err _ _ _ _ _ _ _ hε0 hε hS1 hQ hg hf2b hlb
  exact fin_pos f1 _ E G hf1 hlf hE
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 999 ≤ 1 / 2 ^ 803)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 803 ≤ 2 ^ 999)]) hG2 herr

/-- **The end of the path with a scale `-F`**, `1 ≤ F`. -/
theorem finish_neg (f1 f2 jm : Float) (F : ℕ) (G Q Q0 ε : ℝ) (hf1 : Finite f1.toBits)
    (hf2 : Finite f2.toBits) (hjm : Finite jm.toBits) (hjmb : |value jm.toBits| ≤ 200)
    (hf2b : |value f2.toBits| ≤ |value f1.toBits| / 2 ^ 51)
    (hS1 : |value f1.toBits + value f2.toBits - Q| ≤ |Q| / 2 ^ 76)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 18 / 2 ^ 63) (hQ : |Q - Q0| ≤ ε * |Q0|)
    (hg : |Q0 - G * 2 ^ F| ≤ |G * 2 ^ F| / 2 ^ 62)
    (hQ1 : 1 / 2 ^ 800 ≤ |Q0|) (hQ2 : |Q0| ≤ 2 ^ 800)
    (hF1 : 1 ≤ F) (hF : F ≤ 1500) (hG0 : G ≠ 0)
    (hgap : |G| ≤ 1 / 2 ^ 1022 * (1 - 1 / 2 ^ 48) ∨ 1 / 2 ^ 1022 * (1 + 1 / 2 ^ 48) ≤ |G|) :
    F64SignedRounding.WithinSteps 1 G
      (Float.ofBits (finRes f1 (adjLow f1 f2 jm) (0 - UInt64.ofNat F))).toBits := by
  have h3051 : |value f1.toBits| / 2 ^ 51 ≤ |value f1.toBits| / 2 ^ 30 :=
    div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
  have h30 : |value f2.toBits| ≤ |value f1.toBits| / 2 ^ 30 := hf2b.trans h3051
  obtain ⟨s1, s2, s3, s4⟩ := fin_sizes _ _ _ _ _ _ hε hS1 hQ hg h30 hQ1 hQ2
  obtain ⟨hlf, hlb⟩ := adj_low f1 f2 jm hf1 hf2 hjm hjmb
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 900 ≤ 1 / 2 ^ 803)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 803 ≤ 2 ^ 900)]) h30
  have herr := fin_err _ _ _ _ _ _ _ hε0 hε hS1 hQ hg h30 hlb
  have hflb : |value (adjLow f1 f2 jm).toBits| ≤ |value f1.toBits| / 2 ^ 50 := by
    have := abs_sub_abs_le_abs_sub (value (adjLow f1 f2 jm).toBits) (value f2.toBits)
    have h81 : |value f1.toBits| / 2 ^ 81 + |value f1.toBits| / 2 ^ 51 ≤
        |value f1.toBits| / 2 ^ 50 := by
      have e : |value f1.toBits| / 2 ^ 81 + |value f1.toBits| / 2 ^ 51 =
          |value f1.toBits| * (1 / 2 ^ 81 + 1 / 2 ^ 51) := by ring
      rw [e, show |value f1.toBits| / 2 ^ 50 = |value f1.toBits| * (1 / 2 ^ 50) by ring]
      exact mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _)
    linarith
  exact fin_neg f1 _ F G hf1 hlf hF1 hF hG0
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 999 ≤ 1 / 2 ^ 803)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 803 ≤ 2 ^ 999)]) herr hflb hgap

#print axioms fin_err
#print axioms scale_rel
#print axioms fin_sizes
#print axioms finish_pos
#print axioms finish_neg

end Library.Numerics.Float64.Tgamma.TgammaAccFinish
