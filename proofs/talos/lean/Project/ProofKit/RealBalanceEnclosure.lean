import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Project.ProofKit.RealBalanceEnclosure

theorem residual_bounds (initial final boundary residual : ℝ)
    (initialLo initialHi finalLo finalHi boundaryLo boundaryHi : ℝ)
    (hBalance : final - initial = boundary + residual)
    (hInitial : initialLo ≤ initial ∧ initial ≤ initialHi)
    (hFinal : finalLo ≤ final ∧ final ≤ finalHi)
    (hBoundary : boundaryLo ≤ boundary ∧ boundary ≤ boundaryHi) :
    finalLo - initialHi - boundaryHi ≤ residual ∧
      residual ≤ finalHi - initialLo - boundaryLo := by
  constructor <;> linarith only [hBalance, hInitial.1, hInitial.2,
    hFinal.1, hFinal.2, hBoundary.1, hBoundary.2]

theorem absolute_bound (x lower upper : ℝ) (h : lower ≤ x ∧ x ≤ upper) :
    |x| ≤ max (-lower) upper := by
  apply abs_le.mpr
  exact ⟨(neg_le_neg (le_max_left (-lower) upper)).trans (by simpa using h.1),
    h.2.trans (le_max_right (-lower) upper)⟩

theorem residual_absolute_bound (initial final boundary residual : ℝ)
    (initialLo initialHi finalLo finalHi boundaryLo boundaryHi : ℝ)
    (hBalance : final - initial = boundary + residual)
    (hInitial : initialLo ≤ initial ∧ initial ≤ initialHi)
    (hFinal : finalLo ≤ final ∧ final ≤ finalHi)
    (hBoundary : boundaryLo ≤ boundary ∧ boundary ≤ boundaryHi) :
    |residual| ≤ max (-(finalLo - initialHi - boundaryHi))
      (finalHi - initialLo - boundaryLo) :=
  absolute_bound _ _ _ (residual_bounds _ _ _ _ _ _ _ _ _ _
    hBalance hInitial hFinal hBoundary)

#print axioms residual_bounds
#print axioms absolute_bound
#print axioms residual_absolute_bound
end Project.ProofKit.RealBalanceEnclosure
