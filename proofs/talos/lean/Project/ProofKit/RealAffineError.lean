import Mathlib.Tactic

namespace Project.ProofKit.RealAffineError

theorem subtract_product (ratio state difference roundedDifference product result ed ep er : ℝ)
    (hr : 0 ≤ ratio) (hd : |roundedDifference - difference| ≤ ed)
    (hp : |product - ratio * roundedDifference| ≤ ep)
    (he : |result - (state - product)| ≤ er) :
    |result - (state - ratio * difference)| ≤ ratio * ed + ep + er := by
  have hd' := abs_le.mp hd
  have hp' := abs_le.mp hp
  have he' := abs_le.mp he
  have hlo := mul_le_mul_of_nonneg_left hd'.1 hr
  have hhi := mul_le_mul_of_nonneg_left hd'.2 hr
  apply abs_le.mpr
  constructor <;> linarith only [hlo, hhi, hp'.1, hp'.2, he'.1, he'.2]

#print axioms subtract_product
end Project.ProofKit.RealAffineError
