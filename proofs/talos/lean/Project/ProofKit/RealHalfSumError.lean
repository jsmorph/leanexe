import Mathlib.Tactic

namespace Project.ProofKit.RealHalfSumError

theorem subtract_half_sum (total x y tx ty sum halfSum result ex ey es eh er : ℝ)
    (hx : |tx - x| ≤ ex) (hy : |ty - y| ≤ ey)
    (hs : |sum - (tx + ty)| ≤ es) (hh : |halfSum - sum / 2| ≤ eh)
    (hr : |result - (total - halfSum)| ≤ er) :
    |result - (total - (x + y) / 2)| ≤ er + eh + (es + ex + ey) / 2 := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hs' := abs_le.mp hs
  have hh' := abs_le.mp hh
  have hr' := abs_le.mp hr
  apply abs_le.mpr
  constructor <;> linarith only [hx'.1, hx'.2, hy'.1, hy'.2, hs'.1, hs'.2,
    hh'.1, hh'.2, hr'.1, hr'.2]

#print axioms subtract_half_sum
end Project.ProofKit.RealHalfSumError
