import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace Project.EulerRiemann.RealSoundMargin

theorem error_budget (rho internal M epsilon : ℝ)
    (hr : 0 < rho) (hM : 0 < M) (he : 0 < epsilon)
    (br : rho ≤ M) (bi : internal ≤ M)
    (hmargin : 24 * epsilon * M^3 ≤ internal) :
    epsilon * M^2 ≤ Real.sqrt ((14 / 25) * (internal / rho)) / 16 := by
  let z := epsilon * M^2
  have hz : 0 < z := mul_pos he (sq_pos_of_pos hM)
  have hzM : 24 * z * M ≤ M := by
    dsimp only [z]
    nlinarith only [hmargin, bi]
  have hzUpper : z ≤ 1 / 24 := by
    have h := (mul_le_mul_iff_left₀ hM).mp (show (24 * z) * M ≤ 1 * M by nlinarith only [hzM])
    linarith only [h]
  have hi : 0 < internal := by
    have h := mul_pos he (pow_pos hM 3)
    linarith only [hmargin, h]
  have hquot : 24 * z ≤ internal / rho := by
    apply (le_div_iff₀ hr).mpr
    have h := mul_le_mul_of_nonneg_left br (by positivity : 0 ≤ 24 * z)
    dsimp only [z] at h ⊢
    nlinarith only [h, hmargin]
  have hroot := Real.sqrt_nonneg ((14 / 25) * (internal / rho))
  have hsquare := Real.sq_sqrt (by positivity : 0 ≤ (14 / 25) * (internal / rho))
  have hzz := mul_le_mul_of_nonneg_left hzUpper hz.le
  change z ≤ Real.sqrt ((14 / 25) * (internal / rho)) / 16
  nlinarith only [hquot, hroot, hsquare, hzz, hz]

#print axioms error_budget
end Project.EulerRiemann.RealSoundMargin
