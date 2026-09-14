import Project.Euler2DConservative.RealEigenvectors
import Project.Euler2DConservative.RealJacobian
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Project.Euler2DConservative.RealFlux
open Guard (Vec4 pressure Admissible)
open Module
open scoped Matrix

noncomputable section

def HasEigenbasis (A : Mat4) (values : Fin 4 → ℝ) : Prop :=
  ∃ b : Basis (Fin 4) ℝ Vec4,
    ∀ i, Module.End.HasEigenvector (Matrix.toLin' A) (values i) (b i)

theorem hasEigenbasis_of_matrix (A R : Mat4) (values : Fin 4 → ℝ)
    (he : A * R = R * Matrix.diagonal values) (hd : R.det ≠ 0) :
    HasEigenbasis A values := by
  classical
  have hi := Matrix.linearIndependent_cols_of_det_ne_zero hd
  refine ⟨basisOfPiSpaceOfLinearIndependent hi, ?_⟩
  intro i
  simp only [coe_basisOfPiSpaceOfLinearIndependent]
  rw [Module.End.hasEigenvector_iff]
  refine ⟨?_, LinearIndependent.ne_zero i hi⟩
  rw [Module.End.mem_eigenspace_iff]
  change A *ᵥ R.col i = values i • R.col i
  funext row
  have hentry := congrArg (fun M : Mat4 => M row i) he
  simpa [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum,
    Matrix.diagonal_apply, mul_comm] using hentry

def soundSpeed (U : Vec4) : ℝ := Real.sqrt ((7/5 : ℝ) * pressure U / U 0)

theorem soundSpeed_pos (U : Vec4) (h : Admissible U) : 0 < soundSpeed U :=
  Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) h.2) h.1)

theorem soundSpeed_sq (U : Vec4) (h : Admissible U) :
    soundSpeed U ^ 2 = (7/5 : ℝ)*pressure U / U 0 :=
  Real.sq_sqrt (le_of_lt (div_pos (mul_pos (by norm_num) h.2) h.1))

theorem soundSpeed_acoustic (U : Vec4) (h : Admissible U) :
    soundSpeed U ^ 2 =
      (2/5 : ℝ)*(enthalpy U-(velocity U^2+transverseVelocity U^2)/2) := by
  rw [soundSpeed_sq U h, acoustic_identity U (ne_of_gt h.1)]

def xEigenvectors (U : Vec4) : Mat4 :=
  rightEigenvectors (velocity U) (transverseVelocity U) (enthalpy U) (soundSpeed U)

theorem x_eigenrelation (U : Vec4) (h : Admissible U) :
    xJacobian U * xEigenvectors U =
      xEigenvectors U * Matrix.diagonal (eigenvalues (velocity U) (soundSpeed U)) :=
  reduced_eigenrelation _ _ _ _ (soundSpeed_acoustic U h)

theorem det_xEigenvectors_ne_zero (U : Vec4) (h : Admissible U) :
    (xEigenvectors U).det ≠ 0 :=
  det_rightEigenvectors_ne_zero _ _ _ _ (soundSpeed_acoustic U h)
    (ne_of_gt (soundSpeed_pos U h))

theorem x_hasEigenbasis (U : Vec4) (h : Admissible U) :
    HasEigenbasis (xJacobian U) (eigenvalues (velocity U) (soundSpeed U)) :=
  hasEigenbasis_of_matrix _ _ _ (x_eigenrelation U h) (det_xEigenvectors_ne_zero U h)

theorem x_hyperbolicity (U : Vec4) (h : Admissible U) :
    HasFDerivAt xFlux (matrixCLM (xJacobian U)) U ∧
      HasEigenbasis (xJacobian U) (eigenvalues (velocity U) (soundSpeed U)) :=
  ⟨hasFDerivAt_xFlux U (ne_of_gt h.1), x_hasEigenbasis U h⟩

#print axioms x_hyperbolicity

end
end Project.Euler2DConservative.RealFlux
