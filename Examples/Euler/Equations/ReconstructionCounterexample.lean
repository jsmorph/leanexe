import Examples.Euler.Equations.Flux
import Examples.Euler.Equations.Minmod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Componentwise minmod reconstruction does not preserve positive pressure: three admissible
states, each with internal energy 1/8, give a right face with internal energy -1/4 and pressure
-1/10.  The solvers' limiter therefore tests both faces and halves a common factor. -/

namespace Examples.Euler.Equations.ReconstructionCounterexample

open Examples.Euler.Equations Minmod

noncomputable section

def left : Vec4 := ![1, 0, 0, 1/8]
def center : Vec4 := ![1, 1, 0, 5/8]
def right : Vec4 := ![1, 2, 0, 17/8]

theorem inputs_admissible : Admissible left ∧ Admissible center ∧ Admissible right := by
  change (0 < (1 : ℝ) ∧ 0 < (2/5) * (1/8 - (0^2 + 0^2) / (2 * 1))) ∧
    (0 < (1 : ℝ) ∧ 0 < (2/5) * (5/8 - (1^2 + 0^2) / (2 * 1))) ∧
    (0 < (1 : ℝ) ∧ 0 < (2/5) * (17/8 - (2^2 + 0^2) / (2 * 1)))
  norm_num

theorem reconstructed_right : rightFace left center right = ![1, 3/2, 0, 7/8] := by
  funext i
  fin_cases i <;> norm_num [rightFace, slope, minmod, left, center, right]

theorem negative_internal_energy : internalEnergy (rightFace left center right) = -1/4 := by
  rw [reconstructed_right]
  change (7/8 : ℝ) - ((3/2)^2 + 0^2) / (2 * 1) = -1/4
  norm_num

theorem negative_pressure : pressure (rightFace left center right) = -1/10 := by
  rw [pressure, negative_internal_energy]
  norm_num

end
end Examples.Euler.Equations.ReconstructionCounterexample
