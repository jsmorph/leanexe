import Project.Euler2DConservative.RealFlux
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Project.Euler2DConservative.RealFlux
open scoped Matrix

noncomputable section

def eigenvalues (u c : ℝ) : Fin 4 → ℝ := ![u-c, u, u, u+c]

def rightEigenvectors (u v H c : ℝ) : Mat4 :=
  !![1, 1, 0, 1;
    u-c, u, 0, u+c;
    v, v, 1, v;
    H-u*c, (u^2+v^2)/2, v, H+u*c]

def acousticDefect (u v H c : ℝ) : ℝ :=
  (2/5 : ℝ)*(H-(u^2+v^2)/2)-c^2

theorem reduced_eigensystem_residual (u v H c : ℝ) :
    reducedJacobian u v H * rightEigenvectors u v H c -
      rightEigenvectors u v H c * Matrix.diagonal (eigenvalues u c) =
      !![0, 0, 0, 0;
        acousticDefect u v H c, 0, 0, acousticDefect u v H c;
        0, 0, 0, 0;
        u*acousticDefect u v H c, 0, 0, u*acousticDefect u v H c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reducedJacobian, rightEigenvectors, eigenvalues, acousticDefect,
      Matrix.vecMul_diagonal] <;> ring

theorem reduced_eigenrelation (u v H c : ℝ)
    (hc : c^2 = (2/5 : ℝ)*(H-(u^2+v^2)/2)) :
    reducedJacobian u v H * rightEigenvectors u v H c =
      rightEigenvectors u v H c * Matrix.diagonal (eigenvalues u c) := by
  apply sub_eq_zero.mp
  rw [reduced_eigensystem_residual]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [acousticDefect, hc]

theorem det_rightEigenvectors (u v H c : ℝ) :
    (rightEigenvectors u v H c).det = 2*c*(H-(u^2+v^2)/2) := by
  rw [Matrix.det_succ_row_zero]
  simp [rightEigenvectors, Fin.sum_univ_succ, Matrix.det_fin_three,
    Matrix.submatrix, Fin.succAbove]
  ring

theorem det_rightEigenvectors_ne_zero (u v H c : ℝ)
    (hc : c^2 = (2/5 : ℝ)*(H-(u^2+v^2)/2)) (hc0 : c ≠ 0) :
    (rightEigenvectors u v H c).det ≠ 0 := by
  have he : (rightEigenvectors u v H c).det = 5*c^3 := by
    rw [det_rightEigenvectors]
    calc
      2*c*(H-(u^2+v^2)/2) = 5*c*((2/5 : ℝ)*(H-(u^2+v^2)/2)) := by ring
      _ = 5*c^3 := by rw [← hc]; ring
  rw [he]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hc0)

#print axioms reduced_eigenrelation
#print axioms det_rightEigenvectors_ne_zero

end
end Project.Euler2DConservative.RealFlux
