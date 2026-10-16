import LeanExe.ProofKit.GammaFits

/-!
CORE-MATH's Stirling fits from a threshold `X ≥ 16` on, with the fit's constant and its polynomial
checked together.  A fit's constant `C0` differs from `(log (2 π) - 1)/2` by up to `2 ^ -54` in
`lgamma.c`, and its polynomial `P` from Stirling's twelve coefficients `S` by an amount that
offsets that difference near `X`: `fitRangeOk lo X C0 P ε` bounds
`(m - C0) + t (S - P) (t²)` on `t ∈ [lo, 1/X]`, where `m` is the center of the rational
enclosure of `(log (2 π) - 1)/2`, and adds the enclosure's radius and Stirling's remainder
`104001 / (25 (X - 1) ^ 25)` (`fit_range`).
-/

namespace LeanExe.ProofKit.GammaFitsX

open Real PolyBound GammaBasic GammaStirling GammaThresholds GammaFits

/-- The center and the radius of the enclosure of `(log (2 π) - 1)/2`. -/
def halfLog2PiMid : ℚ := (halfLog2PiLo + halfLog2PiHi) / 2

def halfLog2PiRad : ℚ := (halfLog2PiHi - halfLog2PiLo) / 2

/-- The kernel check that a fit is within `ε` of `lgamma` on `X ≤ x ≤ 1/lo`. -/
def fitRangeOk (lo X C0 : ℚ) (P : List ℚ) (ε : ℚ) (depth : ℕ) : Bool :=
  decide (16 ≤ X) && decide (0 ≤ lo) &&
    check ((halfLog2PiMid - C0) :: PolyCalculus.spread (subP stirCoeffs P)) lo (1 / X)
      (ε - halfLog2PiRad - 104001 / (25 * (X - 1) ^ 25)) depth

theorem fit_range (lo X C0 : ℚ) (P : List ℚ) (ε : ℚ) (depth : ℕ)
    (h : fitRangeOk lo X C0 P ε depth = true) {x : ℝ} (hx : (X : ℝ) ≤ x)
    (hlo : (lo : ℝ) * x ≤ 1) : |lgamma x - fit C0 P x| ≤ ε := by
  simp only [fitRangeOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hX, -⟩, hc⟩ := h
  have hXr : (16 : ℝ) ≤ X := by exact_mod_cast hX
  have hx16 : 16 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have ht1 : (lo : ℝ) ≤ x⁻¹ := by
    rw [← one_div, le_div_iff₀ hx0]
    exact hlo
  have ht2 : x⁻¹ ≤ ((1 / X : ℚ) : ℝ) := by
    push_cast
    rw [one_div]
    exact inv_anti₀ hX0 hx
  have he := check_sound _ lo (1 / X) _ depth hc x⁻¹ ht1 ht2
  rw [eval_cons, PolyCalculus.eval_spread, eval_subP] at he
  have hst := stirling_twelve hx16
  have hrem : 104001 / (25 * (x - 1) ^ 25) ≤ (104001 / (25 * ((X : ℝ) - 1) ^ 25) : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (by norm_num) (pow_pos (by linarith) 25))
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact pow_le_pow_left₀ (by linarith) (by linarith) 25
  obtain ⟨hb1, hb2⟩ := halfLog2Pi_bounds
  have hgap : |(Real.log (2 * π) - 1) / 2 - halfLog2PiMid| ≤ halfLog2PiRad := by
    rw [abs_le]
    simp only [halfLog2PiMid, halfLog2PiRad]
    push_cast
    constructor <;> linarith
  have hsplit : lgamma x - fit C0 P x = (lgamma x - lead x - series stirCoeffs x) +
      ((Real.log (2 * π) - 1) / 2 - halfLog2PiMid) +
      ((((halfLog2PiMid - C0 : ℚ)) : ℝ) +
        x⁻¹ * (eval stirCoeffs (x⁻¹ ^ 2) - eval P (x⁻¹ ^ 2))) := by
    rw [fit, lead, series]
    push_cast
    ring
  rw [hsplit]
  have hεr : ((ε - halfLog2PiRad - 104001 / (25 * (X - 1) ^ 25) : ℚ) : ℝ) =
      ε - halfLog2PiRad - 104001 / (25 * ((X : ℝ) - 1) ^ 25) := by
    push_cast
    ring
  rw [hεr] at he
  calc _ ≤ |lgamma x - lead x - series stirCoeffs x| +
        |(Real.log (2 * π) - 1) / 2 - halfLog2PiMid| +
        |(((halfLog2PiMid - C0 : ℚ)) : ℝ) +
          x⁻¹ * (eval stirCoeffs (x⁻¹ ^ 2) - eval P (x⁻¹ ^ 2))| := abs_add_three _ _ _
    _ ≤ _ := by linarith

#print axioms fit_range

end LeanExe.ProofKit.GammaFitsX
