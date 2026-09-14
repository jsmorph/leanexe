import Project.Euler2DConservative.RealRotation
import Project.Euler2DConservative.RealEigenbasis

namespace Project.Euler2DConservative.RealFlux
open Guard (Vec4 pressure Admissible)
open scoped Matrix

noncomputable section

def normalVelocity (n : Direction) (U : Vec4) : ℝ :=
  (n 0*U 1+n 1*U 2)/U 0

theorem velocity_rotate (n : Direction) (U : Vec4) :
    velocity (rotate n U) = normalVelocity n U := by
  simp [velocity, rotate_eq, normalVelocity]

theorem soundSpeed_rotate (n : Direction) (hn : UnitDirection n) (U : Vec4) :
    soundSpeed (rotate n U) = soundSpeed U := by
  simp only [soundSpeed, pressure_rotate n hn]
  simp [rotate_eq]

def directionalJacobian (n : Direction) (U : Vec4) : Mat4 :=
  (rotation n).transpose * xJacobian (rotate n U) * rotation n

def directionalEigenvectors (n : Direction) (U : Vec4) : Mat4 :=
  (rotation n).transpose * xEigenvectors (rotate n U)

theorem hasFDerivAt_directionalFlux (n : Direction) (hn : UnitDirection n)
    (U : Vec4) (hr : U 0 ≠ 0) :
    HasFDerivAt (directionalFlux n) (matrixCLM (directionalJacobian n U)) U := by
  have hx := hasFDerivAt_xFlux (rotate n U) (by simpa [rotate_eq] using hr)
  have hd := (matrixCLM (rotation n).transpose).hasFDerivAt.comp U
    (hx.comp U (matrixCLM (rotation n)).hasFDerivAt)
  have hf : (fun X => matrixCLM (rotation n).transpose
      (xFlux (matrixCLM (rotation n) X))) = directionalFlux n := by
    funext X
    exact (directionalFlux_rotation n hn X).symm
  change HasFDerivAt (fun X => matrixCLM (rotation n).transpose
    (xFlux (matrixCLM (rotation n) X))) _ U at hd
  rw [hf] at hd
  apply hd.congr_fderiv
  ext V i
  simp [directionalJacobian, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem directional_eigenrelation (n : Direction) (hn : UnitDirection n)
    (U : Vec4) (hU : Admissible U) :
    directionalJacobian n U * directionalEigenvectors n U =
      directionalEigenvectors n U *
        Matrix.diagonal (eigenvalues (normalVelocity n U) (soundSpeed U)) := by
  let P := rotation n
  let A := xJacobian (rotate n U)
  let R := xEigenvectors (rotate n U)
  let D := Matrix.diagonal (eigenvalues (normalVelocity n U) (soundSpeed U))
  have he : A*R = R*D := by
    simpa only [A, R, D, velocity_rotate, soundSpeed_rotate n hn] using
      x_eigenrelation (rotate n U) (admissible_rotate n hn U hU)
  change (P.transpose*A*P)*(P.transpose*R) = (P.transpose*R)*D
  calc
    _ = P.transpose*A*(P*P.transpose)*R := by simp only [Matrix.mul_assoc]
    _ = P.transpose*(A*R) := by
      rw [rotation_mul_transpose n hn, Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [he, Matrix.mul_assoc]

theorem det_directionalEigenvectors_ne_zero (n : Direction) (hn : UnitDirection n)
    (U : Vec4) (hU : Admissible U) :
    (directionalEigenvectors n U).det ≠ 0 := by
  have hp : (rotation n).transpose.det ≠ 0 := by
    have hh := congrArg Matrix.det (transpose_mul_rotation n hn)
    rw [Matrix.det_mul, Matrix.det_one] at hh
    intro hz
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  rw [directionalEigenvectors, Matrix.det_mul]
  exact mul_ne_zero hp (det_xEigenvectors_ne_zero _ (admissible_rotate n hn U hU))

theorem directional_hyperbolicity (n : Direction) (hn : UnitDirection n)
    (U : Vec4) (hU : Admissible U) :
    HasFDerivAt (directionalFlux n) (matrixCLM (directionalJacobian n U)) U ∧
      HasEigenbasis (directionalJacobian n U)
        (eigenvalues (normalVelocity n U) (soundSpeed U)) :=
  ⟨hasFDerivAt_directionalFlux n hn U (ne_of_gt hU.1),
    hasEigenbasis_of_matrix _ _ _ (directional_eigenrelation n hn U hU)
      (det_directionalEigenvectors_ne_zero n hn U hU)⟩

def Hyperbolic (U : Vec4) : Prop :=
  ∀ n, UnitDirection n →
    HasFDerivAt (directionalFlux n) (matrixCLM (directionalJacobian n U)) U ∧
      HasEigenbasis (directionalJacobian n U)
        (eigenvalues (normalVelocity n U) (soundSpeed U))

theorem admissible_hyperbolic (U : Vec4) (hU : Admissible U) : Hyperbolic U :=
  fun n hn => directional_hyperbolicity n hn U hU

#print axioms hasFDerivAt_directionalFlux
#print axioms admissible_hyperbolic

end
end Project.Euler2DConservative.RealFlux
