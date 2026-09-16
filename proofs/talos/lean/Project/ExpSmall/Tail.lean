import Project.ExpSmall.Numerical

namespace Project.ExpSmall
open CodeLib.IEEE64

theorem polynomial_tail_bounds (x : ℝ) (hl : -2 ≤ x) (hu : x ≤ -999/1000) :
    7/45 ≤ polynomialReal x ∧ polynomialReal x ≤ 9/20 := by
  let t := x+2
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t ≤ 1001/1000 := by dsimp [t]; linarith
  have hpoly : polynomialReal x =
      7/45+t/15+t^2/6-t^3/18+t^4/24-t^5/120+t^6/720 := by
    dsimp [polynomialReal, t]
    ring
  rw [hpoly]
  constructor
  · have h23 := mul_nonneg (sq_nonneg t) (show 0 ≤ 3-t by linarith)
    have h45 := mul_nonneg (pow_nonneg ht0 4) (show 0 ≤ 5-t by linarith)
    nlinarith [pow_nonneg ht0 6]
  · have h2 := pow_le_pow_left₀ ht0 ht1 2
    have h4 := pow_le_pow_left₀ ht0 ht1 4
    have h6 := pow_le_pow_left₀ ht0 ht1 6
    norm_num at h2 h4 h6
    nlinarith [pow_nonneg ht0 3, pow_nonneg ht0 5]

theorem polynomial_tail_computed (x : UInt64) (hx : Finite x)
    (hl : -2 ≤ value x) (hu : value x ≤ -999/1000) :
    Finite (polynomial x) ∧ 1/10 ≤ value (polynomial x) ∧
      value (polynomial x) ≤ 46/100 := by
  have h := polynomial_roundoff_two x hx (abs_le.mpr ⟨hl, by linarith⟩)
  have hp := polynomial_tail_bounds (value x) hl hu
  have he := abs_le.mp h.2
  have heps : 32509*arithmeticEpsilon ≤ 1/1000 := by norm_num [arithmeticEpsilon]
  exact ⟨h.1, by linarith, by linarith⟩

#print axioms polynomial_tail_computed
end Project.ExpSmall
