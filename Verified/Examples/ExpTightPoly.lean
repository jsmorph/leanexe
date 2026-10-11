import LeanExe.ProofKit.TaylorRemainder
import Verified.Examples.ExpApproximation

/-!
The approximation error of the polynomial of Arm's `exp` on the residual range of the code.
`ExpApproximation.polynomial_error` bounds it by `2 ^ -56` on `[-1/256, 1/256]` through the Taylor
polynomial of degree 5.  On `abs(r) ≤ 0.002708`, which contains every residual that the
reduction produces, `polynomial_tight` bounds it by `2 ^ -64`: the difference between the
polynomial and the Taylor polynomial of degree 9 has magnitude at most `2 ^ -65` there, which
`PolyBound.check` verifies, and the Taylor remainder is below `2 ^ -80`.
-/

namespace Verified.Examples.ExpTightPoly
open LeanExe.ProofKit PolyBound TaylorRemainder CodeLib.IEEE64

/-- `1 + polynomial r` as a list of rational coefficients. -/
def expP : List ℚ :=
  [1, 1, 9007199254740413 / 2 ^ 54, 6004799503160380 / 2 ^ 55, 6004801545907089 / 2 ^ 57,
    4803841055051799 / 2 ^ 59]

theorem expP_eval (r : ℝ) : eval expP r = 1 + ExpApproximation.polynomial r := by
  obtain ⟨h2, h3, h4, h5⟩ := ExpApproximation.coefficient_values
  simp only [expP, eval_cons, eval_nil, ExpApproximation.polynomial, h2, h3, h4, h5]
  push_cast
  ring

theorem poly_check :
    check (subP (expCoeffs 10) expP) (-2708 / 10 ^ 6) (2708 / 10 ^ 6) (1 / 2 ^ 65) 8 = true := by
  decide +kernel

theorem polynomial_tight (r : ℝ) (hr : |r| ≤ 2708 / 10 ^ 6) :
    |Real.exp r - (1 + ExpApproximation.polynomial r)| ≤ 1 / 2 ^ 64 := by
  have hb := abs_le.mp hr
  have hc := check_sound _ _ _ _ _ poly_check r (by push_cast; linarith) (by push_cast; linarith)
  rw [eval_subP, expP_eval] at hc
  have hrem := exp_remainder r (hr.trans (by norm_num)) 10 (by norm_num)
  have h10 : |r| ^ 10 ≤ (2708 / 10 ^ 6) ^ 10 := pow_le_pow_left₀ (abs_nonneg r) hr 10
  have hk : (2708 / 10 ^ 6 : ℝ) ^ 10 * ((10 + 1 : ℝ) / ((Nat.factorial 10 : ℕ) * (10 : ℕ))) ≤
      1 / 2 ^ 65 := by
    norm_num [Nat.factorial]
  have hrem' : |Real.exp r - eval (expCoeffs 10) r| ≤ 1 / 2 ^ 65 := by
    refine hrem.trans ?_
    calc |r| ^ 10 * ((10 + 1 : ℝ) / ((Nat.factorial 10 : ℕ) * (10 : ℕ))) ≤
        (2708 / 10 ^ 6) ^ 10 * ((10 + 1 : ℝ) / ((Nat.factorial 10 : ℕ) * (10 : ℕ))) :=
          mul_le_mul_of_nonneg_right h10 (by positivity)
      _ ≤ 1 / 2 ^ 65 := hk
  have hc' : |eval (expCoeffs 10) r - (1 + ExpApproximation.polynomial r)| ≤ 1 / 2 ^ 65 := by
    simpa using hc
  calc |Real.exp r - (1 + ExpApproximation.polynomial r)| ≤
      |Real.exp r - eval (expCoeffs 10) r| +
        |eval (expCoeffs 10) r - (1 + ExpApproximation.polynomial r)| := abs_sub_le _ _ _
    _ ≤ 1 / 2 ^ 65 + 1 / 2 ^ 65 := add_le_add hrem' hc'
    _ = 1 / 2 ^ 64 := by norm_num

#print axioms poly_check
#print axioms polynomial_tight

end Verified.Examples.ExpTightPoly
