import Project.Euler2DConservative.RealHyperbolicity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Project.Euler2DConservative.RealFlux
open Guard (Vec4 Admissible)
open scoped Matrix
noncomputable section

def directionalLeftEigenvectors (n : Direction) (U : Vec4) : Mat4 :=
  (directionalEigenvectors n U)⁻¹

theorem directional_eigenvector_inverses (n : Direction) (hn : UnitDirection n)
    (U : Vec4) (hU : Admissible U) :
    directionalLeftEigenvectors n U*directionalEigenvectors n U = 1 ∧
    directionalEigenvectors n U*directionalLeftEigenvectors n U = 1 := by
  have hd : IsUnit (directionalEigenvectors n U).det :=
    isUnit_iff_ne_zero.mpr (det_directionalEigenvectors_ne_zero n hn U hU)
  exact ⟨Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

theorem directional_left_eigenrelation (n : Direction) (hn : UnitDirection n)
    (U : Vec4) (hU : Admissible U) :
    directionalLeftEigenvectors n U*directionalJacobian n U =
      Matrix.diagonal (eigenvalues (normalVelocity n U) (soundSpeed U))*
        directionalLeftEigenvectors n U := by
  obtain ⟨hl, hr⟩ := directional_eigenvector_inverses n hn U hU
  let L := directionalLeftEigenvectors n U
  let R := directionalEigenvectors n U
  let A := directionalJacobian n U
  let D := Matrix.diagonal (eigenvalues (normalVelocity n U) (soundSpeed U))
  have he : A*R = R*D := directional_eigenrelation n hn U hU
  change L*A = D*L
  calc
    L*A = L*A*(R*L) := by rw [hr, Matrix.mul_one]
    _ = L*(A*R)*L := by simp only [Matrix.mul_assoc]
    _ = L*(R*D)*L := by rw [he]
    _ = (L*R)*D*L := by simp only [Matrix.mul_assoc]
    _ = D*L := by rw [hl, Matrix.one_mul]

theorem directional_characteristic_reconstruction (n : Direction) (hn : UnitDirection n)
    (U : Vec4) (hU : Admissible U) (jump : Vec4) :
    directionalEigenvectors n U *ᵥ (directionalLeftEigenvectors n U *ᵥ jump) = jump := by
  rw [Matrix.mulVec_mulVec, (directional_eigenvector_inverses n hn U hU).2,
    Matrix.one_mulVec]

#print axioms directional_left_eigenrelation
#print axioms directional_characteristic_reconstruction
end
end Project.Euler2DConservative.RealFlux
