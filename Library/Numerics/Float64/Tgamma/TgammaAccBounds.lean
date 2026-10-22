import Library.Numerics.Float64.Tgamma.TgammaRefl9
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
Bounds for the assembly of the accurate path of `Tgamma`.  `|Γ v| ≥ 2 ^ -1018` between -170 and 0
by the reflection formula and `170! ≤ 3 · 2 ^ 1018` (`gamma_neg_lower`), and `Γ v ≥ 1 / (v (v + 1))`
for `v > 0` (`gamma_pos_lower`), so `|Γ|` keeps away from `2 ^ -1022` from -170 on, and
`TgammaRefl9.refl_gap` covers `(-184, -170)` (`acc_gap`).  `rel_trans`, `rel_div`, and `rel_mul`
compose relative errors.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccBounds
open CodeLib.IEEE64 LeanExe.ProofKit Real

set_option exponentiation.threshold 4096

theorem fact170 : (Nat.factorial 170 : ℝ) ≤ 3 * 2 ^ 1018 := by
  have h : Nat.factorial 170 ≤ 3 * 2 ^ 1018 := by decide +kernel
  exact_mod_cast h

theorem gamma_three : Gamma 3 = 2 := by
  rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

/-- `Γ (1 - v)` is at most `170!` for `-170 < v < 0`. -/
theorem gamma_one_sub_le (v : ℝ) (h1 : -170 < v) (h2 : v < 0) :
    Gamma (1 - v) ≤ (Nat.factorial 170 : ℝ) := by
  have h171 : Gamma (170 + 1) = (Nat.factorial 170 : ℝ) := by
    exact_mod_cast Gamma_nat_eq_factorial 170
  rcases le_or_gt 2 (1 - v) with h | h
  · rw [← h171]
    exact Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr h) (Set.mem_Ici.mpr (by norm_num))
      (by linarith)
  · have hadd := Gamma_add_one (s := 1 - v) (by linarith : (0 : ℝ) < 1 - v).ne'
    have h3 : Gamma (1 - v + 1) ≤ Gamma 3 :=
      Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (by linarith))
        (Set.mem_Ici.mpr (by norm_num)) (by linarith)
    rw [gamma_three, hadd] at h3
    have hpos : 0 < Gamma (1 - v) := Gamma_pos_of_pos (by linarith)
    have h4 : Gamma (1 - v) ≤ 2 := by nlinarith
    have h5 : (2 : ℝ) ≤ (Nat.factorial 170 : ℝ) := by
      have := Nat.self_le_factorial 170
      have h6 : ((170 : ℕ) : ℝ) ≤ (Nat.factorial 170 : ℝ) := by exact_mod_cast this
      push_cast at h6
      linarith
    linarith

/-- **`|Γ|` between -170 and 0** is at least `2 ^ -1018`. -/
theorem gamma_neg_lower (v : ℝ) (h1 : -170 < v) (h2 : v < 0) (hnint : ∀ n : ℤ, v ≠ n) :
    1 / 2 ^ 1018 ≤ |Gamma v| := by
  have hG1pos : 0 < Gamma (1 - v) := Gamma_pos_of_pos (by linarith)
  have hsin : sin (π * v) ≠ 0 := by
    intro h
    rw [sin_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have h' : (n : ℝ) * π = v * π := by rw [hn]; ring
    exact hnint n (mul_right_cancel₀ pi_ne_zero h').symm
  have hG : Gamma v = π / sin (π * v) / Gamma (1 - v) := by
    rw [← Gamma_mul_Gamma_one_sub, mul_div_cancel_right₀ _ hG1pos.ne']
  have hsinp : 0 < |sin (π * v)| := abs_pos.mpr hsin
  have hsinb : |sin (π * v)| ≤ 1 := abs_sin_le_one _
  rw [hG, abs_div, abs_div, abs_of_pos pi_pos, abs_of_pos hG1pos, div_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : |sin (π * v)| * Gamma (1 - v) ≤ Gamma (1 - v) :=
    mul_le_of_le_one_left hG1pos.le hsinb
  have h4 := gamma_one_sub_le v h1 h2
  have h5 := fact170
  have h6 : (3 : ℝ) * 2 ^ 1018 ≤ π * 2 ^ 1018 :=
    mul_le_mul_of_nonneg_right pi_gt_three.le (by positivity)
  linarith

/-- **`Γ` above 0** is at least `1 / (v (v + 1))`. -/
theorem gamma_pos_lower (v : ℝ) (h0 : 0 < v) : 1 / (v * (v + 1)) ≤ Gamma v := by
  have h2 : Gamma 2 ≤ Gamma (v + 1 + 1) :=
    Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (by norm_num))
      (Set.mem_Ici.mpr (by linarith)) (by linarith)
  rw [Gamma_two, Gamma_add_one (s := v + 1) (by linarith : (0 : ℝ) < v + 1).ne',
    Gamma_add_one (s := v) h0.ne'] at h2
  rw [div_le_iff₀ (mul_pos h0 (by linarith))]
  linarith [(by ring : (v + 1) * (v * Gamma v) = Gamma v * (v * (v + 1)))]

/-- **The gap around `2 ^ -1022`** for every double from -184 to `2 ^ 8` other than an
integer. -/
theorem acc_gap (hGap : TgammaRefl4.SubnormalGap) (x : Float) (hnint : ∀ n : ℤ, value x.toBits ≠ n)
    (hlo : -184 < value x.toBits) (hhi : value x.toBits ≤ 2 ^ 8) :
    |Gamma (value x.toBits)| ≤ 1 / 2 ^ 1022 * (1 - 1 / 2 ^ 48) ∨
      1 / 2 ^ 1022 * (1 + 1 / 2 ^ 48) ≤ |Gamma (value x.toBits)| := by
  rcases lt_or_ge (value x.toBits) (-170) with h | h
  · exact TgammaRefl9.refl_gap hGap x hlo h
  · right
    have hne : value x.toBits ≠ -170 := by
      have := hnint (-170); push_cast at this; exact this
    rcases lt_or_ge (value x.toBits) 0 with h0 | h0
    · have := gamma_neg_lower _ (lt_of_le_of_ne h (Ne.symm hne)) h0 hnint
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1022 * (1 + 1 / 2 ^ 48) ≤ 1 / 2 ^ 1018)]
    · have hpos : 0 < value x.toBits := by
        rcases h0.lt_or_eq with h0 | h0
        · exact h0
        · exact absurd (by rw [← h0]; simp : value x.toBits = ((0 : ℤ) : ℝ)) (hnint 0)
      have h1 := gamma_pos_lower _ hpos
      rw [abs_of_pos (Gamma_pos_of_pos hpos)]
      have h2 : 1 / (2 ^ 8 * (2 ^ 8 + 1)) ≤ 1 / (value x.toBits * (value x.toBits + 1)) := by
        apply one_div_le_one_div_of_le (mul_pos hpos (by linarith))
        nlinarith
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1022 * (1 + 1 / 2 ^ 48) ≤ 1 / (2 ^ 8 * (2 ^ 8 + 1)))]

/-- Two relative errors in sequence. -/
theorem rel_trans (a b c α β : ℝ) (hα : 0 ≤ α) (h1 : |a - b| ≤ α * |b|)
    (h2 : |b - c| ≤ β * |c|) : |a - c| ≤ (α + β + α * β) * |c| := by
  have hb : |b| ≤ (1 + β) * |c| := by linarith [abs_sub_abs_le_abs_sub b c]
  have h3 := abs_sub_le a b c
  have h4 := mul_le_mul_of_nonneg_left hb hα
  linarith

/-- The quotient of two numbers with relative errors `α` and `β ≤ 1/2`. -/
theorem rel_div (P A Wd W α β : ℝ) (hW : W ≠ 0) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hβ1 : β ≤ 1 / 2)
    (h1 : |P - A| ≤ α * |A|) (h2 : |Wd - W| ≤ β * |W|) :
    |P / Wd - A / W| ≤ (α + β) * (1 + 2 * β) * |A / W| := by
  have hWp : 0 < |W| := abs_pos.mpr hW
  have hWd : (1 - β) * |W| ≤ |Wd| := by
    have := abs_sub_abs_le_abs_sub W Wd
    rw [abs_sub_comm] at this
    linarith
  have hWdp : 0 < |Wd| := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - β) hWp.le]
  have hWd0 : Wd ≠ 0 := abs_pos.mp hWdp
  have heq : P / Wd - A / W = ((P - A) * W - A * (Wd - W)) / (Wd * W) := by
    rw [div_sub_div _ _ hWd0 hW]
    ring
  have hnum : |(P - A) * W - A * (Wd - W)| ≤ (α + β) * |A| * |W| := by
    calc _ ≤ |(P - A) * W| + |A * (Wd - W)| := abs_sub _ _
      _ = |P - A| * |W| + |A| * |Wd - W| := by rw [abs_mul, abs_mul]
      _ ≤ α * |A| * |W| + |A| * (β * |W|) :=
          add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ = (α + β) * |A| * |W| := by ring
  have hW2 : |W| ≤ (1 + 2 * β) * |Wd| := by
    nlinarith [mul_nonneg (mul_nonneg hβ (by linarith : (0 : ℝ) ≤ 1 - 2 * β)) (abs_nonneg W),
      mul_le_mul_of_nonneg_left hWd (by linarith : (0 : ℝ) ≤ 1 + 2 * β)]
  rw [heq, abs_div, abs_mul Wd W, div_le_iff₀ (mul_pos hWdp hWp), abs_div]
  have hr : (α + β) * (1 + 2 * β) * (|A| / |W|) * (|Wd| * |W|) =
      (α + β) * |A| * ((1 + 2 * β) * |Wd|) := by
    calc (α + β) * (1 + 2 * β) * (|A| / |W|) * (|Wd| * |W|)
        = (α + β) * (1 + 2 * β) * |A| * |Wd| * (|W| / |W|) := by ring
      _ = _ := by rw [div_self hWp.ne']; ring
  rw [hr]
  calc _ ≤ (α + β) * |A| * |W| := hnum
    _ ≤ _ := mul_le_mul_of_nonneg_left hW2 (by positivity)

/-- The product of two numbers with relative errors `α` and `β`. -/
theorem rel_mul (P A Wd W α β : ℝ) (hα : 0 ≤ α) (h1 : |P - A| ≤ α * |A|)
    (h2 : |Wd - W| ≤ β * |W|) : |P * Wd - A * W| ≤ (α + β + α * β) * |A * W| := by
  have hWd : |Wd| ≤ (1 + β) * |W| := by linarith [abs_sub_abs_le_abs_sub Wd W]
  have heq : P * Wd - A * W = (P - A) * Wd + A * (Wd - W) := by ring
  rw [heq, abs_mul A W]
  calc _ ≤ |(P - A) * Wd| + |A * (Wd - W)| := abs_add_le _ _
    _ = |P - A| * |Wd| + |A| * |Wd - W| := by rw [abs_mul, abs_mul]
    _ ≤ (α * |A|) * ((1 + β) * |W|) + |A| * (β * |W|) :=
        add_le_add (mul_le_mul h1 hWd (abs_nonneg _) (mul_nonneg hα (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = (α + β + α * β) * (|A| * |W|) := by ring

#print axioms fact170
#print axioms gamma_neg_lower
#print axioms gamma_pos_lower
#print axioms acc_gap
#print axioms rel_trans
#print axioms rel_div
#print axioms rel_mul

end Library.Numerics.Float64.Tgamma.TgammaAccBounds
