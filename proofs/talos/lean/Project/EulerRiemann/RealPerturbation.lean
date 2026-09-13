import Project.EulerRiemann.RealRusanov
import Project.ProofKit.RealProductError

namespace Project.EulerRiemann.RealRusanov
open Project.Euler2DConservative.Guard (Vec4 internalEnergy Admissible)
open Project.ProofKit.RealProductError (product_perturbation)

theorem energyMargin_perturbation (q next : Vec4) (bound error : ℝ)
    (hq : ∀ i, |q i| ≤ bound) (hError : ∀ i, |next i - q i| ≤ error) :
    |energyMargin next - energyMargin q| ≤ 8 * bound * error + 4 * error^2 := by
  have hp := product_perturbation (q 0) (q 3) (next 0) (next 3) bound error
    (hq 0) (hq 3) (hError 0) (hError 3)
  have hx := product_perturbation (q 1) (q 1) (next 1) (next 1) bound error
    (hq 1) (hq 1) (hError 1) (hError 1)
  have hy := product_perturbation (q 2) (q 2) (next 2) (next 2) bound error
    (hq 2) (hq 2) (hError 2) (hError 2)
  have hTriangle :
      |2 * (next 0 * next 3 - q 0 * q 3) -
          (next 1 * next 1 - q 1 * q 1) - (next 2 * next 2 - q 2 * q 2)| ≤
        2 * |next 0 * next 3 - q 0 * q 3| +
          |next 1 * next 1 - q 1 * q 1| + |next 2 * next 2 - q 2 * q 2| := by
    calc
      _ ≤ |2 * (next 0 * next 3 - q 0 * q 3) - (next 1 * next 1 - q 1 * q 1)| +
          |next 2 * next 2 - q 2 * q 2| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (2 * (next 0 * next 3 - q 0 * q 3) -
            (next 1 * next 1 - q 1 * q 1)) (-(next 2 * next 2 - q 2 * q 2))
      _ ≤ |2 * (next 0 * next 3 - q 0 * q 3)| +
          |next 1 * next 1 - q 1 * q 1| + |next 2 * next 2 - q 2 * q 2| :=
        add_le_add (by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le (2 * (next 0 * next 3 - q 0 * q 3))
              (-(next 1 * next 1 - q 1 * q 1))) le_rfl
      _ = _ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have heq : energyMargin next - energyMargin q =
      2 * (next 0 * next 3 - q 0 * q 3) -
        (next 1 * next 1 - q 1 * q 1) - (next 2 * next 2 - q 2 * q 2) := by
    simp only [energyMargin]
    ring
  rw [heq]
  linarith

theorem admissible_of_perturbation (q next : Vec4) (bound error : ℝ)
    (hq : ∀ i, |q i| ≤ bound) (hError : ∀ i, |next i - q i| ≤ error)
    (hDensity : error < q 0)
    (hMargin : 8 * bound * error + 4 * error^2 < energyMargin q) :
    Admissible next := by
  have hr : 0 < next 0 := by linarith [(abs_le.mp (hError 0)).1]
  have hm : 0 < energyMargin next := by
    linarith [(abs_le.mp (energyMargin_perturbation q next bound error hq hError)).1]
  have hi : 0 < internalEnergy next := by
    rw [internalEnergy_eq_margin next (ne_of_gt hr)]
    exact div_pos hm (by positivity)
  exact ⟨hr, mul_pos (by norm_num : (0 : ℝ) < 2 / 5) hi⟩

#print axioms product_perturbation
#print axioms energyMargin_perturbation
#print axioms admissible_of_perturbation
end Project.EulerRiemann.RealRusanov
