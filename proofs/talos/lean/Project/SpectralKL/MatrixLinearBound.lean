import Project.SpectralKL.MatrixPreconditioned

namespace Project.SpectralKL.MatrixPreconditioned
open Matrix Finset MatrixIteration
open scoped Matrix
variable {m : Nat}

/-- A squared-residual bound also controls the linear inverse-quadratic
approximation. This avoids forming a quadratic polynomial in the iterate. -/
theorem linear_error (H : Matrix (Fin m) (Fin m) ℝ) (d x : Fin m → ℝ)
    (eta : ℝ) (he : 0 < eta) (hH : Residual.Symmetric H) (hc : Residual.Coercive H eta)
    (q : ℝ) (hq : 0 ≤ q) (hr : normSq (d-H *ᵥ x) ≤ q^2*normSq d) :
    |d ⬝ᵥ x-Residual.quadratic H d| ≤ q*normSq d/eta := by
  let y := H⁻¹ *ᵥ d
  let e := y-x
  have hy : H *ᵥ y = d := Residual.solve H (Residual.posDef H hH eta he hc) d
  have hre : H *ᵥ e = d-H *ᵥ x := by simp [e,Matrix.mulVec_sub,hy]
  have hu := Residual.residual_upper H eta he hc e
  have hl := hc e
  rw [hre] at hu
  have hn : eta^2*normSq e ≤ normSq (d-H *ᵥ x) := by
    have hh := (le_div_iff₀ he).mp hu
    change _ ≤ normSq (d-H *ᵥ x) at hh
    change eta*normSq e ≤ _ at hl
    rw [hre] at hl
    nlinarith [mul_le_mul_of_nonneg_left hl he.le]
  have hcs : (d ⬝ᵥ e)^2 ≤ normSq d*normSq e := by
    simpa only [normSq,dotProduct,← pow_two] using
      sum_mul_sq_le_sq_mul_sq univ d e
  have hs : (eta*(d ⬝ᵥ e))^2 ≤ (q*normSq d)^2 := calc
    _ = eta^2*(d ⬝ᵥ e)^2 := by ring
    _ ≤ eta^2*(normSq d*normSq e) := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = normSq d*(eta^2*normSq e) := by ring
    _ ≤ normSq d*normSq (d-H *ᵥ x) := mul_le_mul_of_nonneg_left hn (normSq_nonneg _)
    _ ≤ normSq d*(q^2*normSq d) := mul_le_mul_of_nonneg_left hr (normSq_nonneg _)
    _ = (q*normSq d)^2 := by ring
  have hb : |eta*(d ⬝ᵥ e)| ≤ q*normSq d :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hq (normSq_nonneg _))).mp (by simpa only [sq_abs] using hs)
  rw [abs_mul,abs_of_pos he] at hb
  have hid : |d ⬝ᵥ x-Residual.quadratic H d| = |d ⬝ᵥ e| := by
    simp only [e,Residual.quadratic,dotProduct_sub,y]
    exact abs_sub_comm _ _
  rw [hid]
  exact (le_div_iff₀ he).mpr (by nlinarith [hb])

#print axioms linear_error
end Project.SpectralKL.MatrixPreconditioned
