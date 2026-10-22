import Library.Numerics.Float64.Tgamma.TgammaApprox
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
The size of `Γ` on the ranges of the accurate path.  On each row `[j, j + 1]` of
`TgammaApprox.accRanges`, `(j - 1)! ≥ 2 ^ eoff / 16` (`fact_ok`, a kernel check), and `Γ` increases
from 2 on, so `Γ y ≥ 2 ^ eoff / 16` there (`gamma_range_lo`).  `AccRangeFact` then puts the
polynomial `accPoly` at least `1/17` (`accPoly_lo`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccGamma
open TgammaApprox

theorem fact_ok : ∀ r ∈ accRanges, 2 ^ r.2.2.2.2.2 ≤ 16 * (r.2.2.2.2.1 - 1).factorial ∧
    4 ≤ r.2.2.2.2.1 := by
  decide +kernel

/-- `Γ` on a range of the accurate path. -/
theorem gamma_range_lo (oh imax ol jmax j eoff : ℕ) (hr : (oh, imax, ol, jmax, j, eoff) ∈ accRanges)
    (y : ℝ) (hy : (j : ℝ) ≤ y) : (2 : ℝ) ^ eoff / 16 ≤ Real.Gamma y := by
  obtain ⟨hf, hj⟩ := fact_ok _ hr
  dsimp only at hf hj
  have hj' : (4 : ℝ) ≤ j := by exact_mod_cast hj
  have hmono : Real.Gamma j ≤ Real.Gamma y :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) hy
  have hfact : Real.Gamma j = ((j - 1).factorial : ℝ) := by
    have := Real.Gamma_nat_eq_factorial (j - 1)
    rw [← this]
    congr 1
    rw [Nat.cast_sub (by omega)]
    ring
  have h16 : (2 : ℝ) ^ eoff ≤ 16 * ((j - 1).factorial : ℝ) := by exact_mod_cast hf
  rw [hfact] at hmono
  linarith

/-- **The polynomial of a range is at least `1/17`.** -/
theorem accPoly_lo (hA : AccRangeFact) (oh imax ol jmax j eoff : ℕ)
    (hr : (oh, imax, ol, jmax, j, eoff) ∈ accRanges) (d : ℝ) (hd : |d| ≤ 1) :
    1 / 17 ≤ accPoly oh imax ol jmax d ∧
      |Real.Gamma (j + (1 + d) / 2) - 2 ^ eoff * accPoly oh imax ol jmax d| ≤
        1 / 2 ^ 62 * Real.Gamma (j + (1 + d) / 2) := by
  have h := hA oh imax ol jmax j eoff hr d hd
  refine ⟨?_, h⟩
  have hd1 := (abs_le.mp hd).1
  have hG := gamma_range_lo oh imax ol jmax j eoff hr (j + (1 + d) / 2) (by linarith)
  have h2 := (abs_le.mp h).2
  have hpos : (0 : ℝ) < 2 ^ eoff := by positivity
  have : 2 ^ eoff * (1 / 17) ≤ 2 ^ eoff * accPoly oh imax ol jmax d := by
    have : (2 : ℝ) ^ eoff / 16 * (1 - 1 / 2 ^ 62) ≤ 2 ^ eoff * accPoly oh imax ol jmax d := by
      nlinarith
    nlinarith
  exact le_of_mul_le_mul_left this hpos

#print axioms fact_ok
#print axioms accPoly_lo

end Library.Numerics.Float64.Tgamma.TgammaAccGamma
