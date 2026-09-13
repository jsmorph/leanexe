import Project.EulerRiemann.RealRusanov

namespace Project.EulerRiemann.RealRusanov
open Project.Euler2DConservative.Guard (Vec4 internalEnergy)

theorem margin_eq_internalEnergy (q : Vec4) (hr : q 0 ≠ 0) :
    energyMargin q = 2 * q 0 * internalEnergy q := by
  rw [internalEnergy_eq_margin q hr]
  field_simp

theorem margin_weight_lower (q reference : Vec4) (weight : ℝ)
    (hw : 0 < weight) (hr : 0 < q 0) (hi : 0 ≤ internalEnergy q)
    (hRho : weight * q 0 ≤ reference 0)
    (hInternal : weight * internalEnergy q ≤ internalEnergy reference) :
    weight^2 * energyMargin q ≤ energyMargin reference := by
  have hRef : 0 < reference 0 := (mul_pos hw hr).trans_le hRho
  have hp := mul_le_mul hRho hInternal (mul_nonneg hw.le hi) hRef.le
  rw [margin_eq_internalEnergy q (ne_of_gt hr), margin_eq_internalEnergy reference (ne_of_gt hRef)]
  nlinarith only [hp]

#print axioms margin_eq_internalEnergy
#print axioms margin_weight_lower
end Project.EulerRiemann.RealRusanov
