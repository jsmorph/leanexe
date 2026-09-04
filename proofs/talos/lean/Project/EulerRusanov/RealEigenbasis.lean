import Project.EulerRusanov.RealMatrices
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Complete real eigenbasis for the conservative Euler Jacobian

This module supplies the substantive hyperbolicity certificate missing from a
mere assertion that three scalar expressions are real.  It proves an explicit
matrix eigenrelation, computes the determinant of the right-eigenvector
matrix, constructs an actual basis of conservative state space, and packages
its vectors using Mathlib's `Module.End.HasEigenvector` predicate.

The algebraic core is stated for independent real parameters `u`, `H`, and
`c`.  Its sole thermodynamic hypothesis is

`c^2 = (2 / 5) * (H - u^2 / 2)`.

The final section discharges that hypothesis using the conservative Euler
definitions and positive density and pressure.
-/

namespace Project.EulerRusanov.RealEigenbasis

open Project.EulerRusanov.RealConservative
open Project.EulerRusanov.RealMatrices
open Module
open scoped Matrix
open scoped Classical

noncomputable section

/-! ## Algebraic characteristic data -/

/-- The three characteristic values, ordered as the left acoustic, contact,
and right acoustic fields. -/
def eigenvalues (u c : ℝ) : Fin 3 → ℝ :=
  ![u - c, u, u + c]

@[simp] theorem eigenvalues_zero (u c : ℝ) :
    eigenvalues u c 0 = u - c := by
  rfl

@[simp] theorem eigenvalues_one (u c : ℝ) :
    eigenvalues u c 1 = u := by
  rfl

@[simp] theorem eigenvalues_two (u c : ℝ) :
    eigenvalues u c 2 = u + c := by
  rfl

/-- Diagonal matrix of characteristic values. -/
def eigenvalueMatrix (u c : ℝ) : Mat3 :=
  Matrix.diagonal (eigenvalues u c)

/-- Right-eigenvector matrix.  Its columns are respectively

`(1, u-c, H-u*c)`, `(1, u, u^2/2)`, and `(1, u+c, H+u*c)`.
-/
def rightEigenvectors (u H c : ℝ) : Mat3 :=
  !![
    1,       1,       1;
    u - c,   u,       u + c;
    H - u*c, u^2 / 2, H + u*c
  ]

theorem rightEigenvectors_col_zero (u H c : ℝ) :
    (rightEigenvectors u H c).col 0 = ![1, u - c, H - u * c] := by
  funext i
  fin_cases i <;> rfl

theorem rightEigenvectors_col_one (u H c : ℝ) :
    (rightEigenvectors u H c).col 1 = ![1, u, u ^ 2 / 2] := by
  funext i
  fin_cases i <;> rfl

theorem rightEigenvectors_col_two (u H c : ℝ) :
    (rightEigenvectors u H c).col 2 = ![1, u + c, H + u * c] := by
  funext i
  fin_cases i <;> rfl

/-- The sole residual in the acoustic-column calculation. -/
def acousticDefect (u H c : ℝ) : ℝ :=
  ((2 : ℝ) / 5) * (H - u ^ 2 / 2) - c ^ 2

/-- Before imposing the acoustic relation, all nine entries of the matrix
eigenrelation reduce to one scalar defect.  Recording this residual explicitly
makes the later proof independent of nonlinear proof-search heuristics. -/
theorem reduced_eigensystem_residual (u H c : ℝ) :
    reducedJacobian u H * rightEigenvectors u H c -
        rightEigenvectors u H c * eigenvalueMatrix u c =
      !![
        0, 0, 0;
        acousticDefect u H c, 0, acousticDefect u H c;
        u * acousticDefect u H c, 0, u * acousticDefect u H c
      ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reducedJacobian, rightEigenvectors, eigenvalueMatrix,
      eigenvalues, acousticDefect, Matrix.vecMul_diagonal] <;>
    ring

/-- Matrix form of all three right-eigenvector equations. -/
theorem reducedJacobian_mul_rightEigenvectors
    (u H c : ℝ)
    (hacoustic : c ^ 2 = ((2 : ℝ) / 5) * (H - u ^ 2 / 2)) :
    reducedJacobian u H * rightEigenvectors u H c =
      rightEigenvectors u H c * eigenvalueMatrix u c := by
  apply sub_eq_zero.mp
  rw [reduced_eigensystem_residual]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [acousticDefect, hacoustic]

/-- Extract one column eigenvector equation from a matrix diagonalization
identity. -/
private theorem mulVec_col_of_mul_eq_mul_diagonal
    (A R : Mat3) (values : Fin 3 → ℝ)
    (hmatrix : A * R = R * Matrix.diagonal values) (i : Fin 3) :
    A *ᵥ R.col i = values i • R.col i := by
  funext row
  have hentry := congrArg (fun M : Mat3 => M row i) hmatrix
  simpa [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum,
    Matrix.diagonal_apply, mul_comm] using hentry

/-- Each displayed column is an eigenvector equation for the reduced
Jacobian.  Nonzeroness is established below from the determinant. -/
theorem reducedJacobian_mulVec_rightEigenvector
    (u H c : ℝ)
    (hacoustic : c ^ 2 = ((2 : ℝ) / 5) * (H - u ^ 2 / 2))
    (i : Fin 3) :
    reducedJacobian u H *ᵥ (rightEigenvectors u H c).col i =
      eigenvalues u c i • (rightEigenvectors u H c).col i := by
  apply mulVec_col_of_mul_eq_mul_diagonal
  exact reducedJacobian_mul_rightEigenvectors u H c hacoustic

/-! ## Determinant, independence, and the parameterized basis -/

/-- Determinant of the displayed right-eigenvector matrix. -/
theorem det_rightEigenvectors (u H c : ℝ) :
    (rightEigenvectors u H c).det =
      2 * c * (H - u ^ 2 / 2) := by
  rw [Matrix.det_fin_three]
  simp [rightEigenvectors]
  ring

/-- Under the acoustic relation, the determinant is `5*c^3`. -/
theorem det_rightEigenvectors_eq_five_mul_cube
    (u H c : ℝ)
    (hacoustic : c ^ 2 = ((2 : ℝ) / 5) * (H - u ^ 2 / 2)) :
    (rightEigenvectors u H c).det = 5 * c ^ 3 := by
  rw [det_rightEigenvectors]
  calc
    2 * c * (H - u ^ 2 / 2) =
        5 * c * (((2 : ℝ) / 5) * (H - u ^ 2 / 2)) := by ring
    _ = 5 * c * c ^ 2 := by rw [← hacoustic]
    _ = 5 * c ^ 3 := by ring

theorem det_rightEigenvectors_ne_zero
    (u H c : ℝ)
    (hacoustic : c ^ 2 = ((2 : ℝ) / 5) * (H - u ^ 2 / 2))
    (hc : c ≠ 0) :
    (rightEigenvectors u H c).det ≠ 0 := by
  rw [det_rightEigenvectors_eq_five_mul_cube u H c hacoustic]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hc)

theorem rightEigenvectors_linearIndependent
    (u H c : ℝ)
    (hacoustic : c ^ 2 = ((2 : ℝ) / 5) * (H - u ^ 2 / 2))
    (hc : c ≠ 0) :
    LinearIndependent ℝ (rightEigenvectors u H c).col :=
  Matrix.linearIndependent_cols_of_det_ne_zero
    (det_rightEigenvectors_ne_zero u H c hacoustic hc)

/-- The three displayed columns form an actual basis whenever the acoustic
relation holds and the sound speed is nonzero. -/
noncomputable def rightEigenbasis
    (u H c : ℝ)
    (hacoustic : c ^ 2 = ((2 : ℝ) / 5) * (H - u ^ 2 / 2))
    (hc : c ≠ 0) : Basis (Fin 3) ℝ Vec3 :=
  basisOfPiSpaceOfLinearIndependent
    (rightEigenvectors_linearIndependent u H c hacoustic hc)

@[simp] theorem coe_rightEigenbasis
    (u H c : ℝ)
    (hacoustic : c ^ 2 = ((2 : ℝ) / 5) * (H - u ^ 2 / 2))
    (hc : c ≠ 0) :
    ⇑(rightEigenbasis u H c hacoustic hc) =
      (rightEigenvectors u H c).col := by
  simp only [rightEigenbasis, coe_basisOfPiSpaceOfLinearIndependent]

/-- The parameterized columns satisfy Mathlib's nonzero eigenvector
predicate. -/
theorem reducedJacobian_hasEigenvector
    (u H c : ℝ)
    (hacoustic : c ^ 2 = ((2 : ℝ) / 5) * (H - u ^ 2 / 2))
    (hc : c ≠ 0) (i : Fin 3) :
    Module.End.HasEigenvector (Matrix.toLin' (reducedJacobian u H))
      (eigenvalues u c i) ((rightEigenvectors u H c).col i) := by
  rw [Module.End.hasEigenvector_iff]
  refine ⟨?_, LinearIndependent.ne_zero i
    (rightEigenvectors_linearIndependent u H c hacoustic hc)⟩
  rw [Module.End.mem_eigenspace_iff]
  simpa only [Matrix.toLin'_apply] using
    reducedJacobian_mulVec_rightEigenvector u H c hacoustic i

theorem rightEigenbasis_hasEigenvector
    (u H c : ℝ)
    (hacoustic : c ^ 2 = ((2 : ℝ) / 5) * (H - u ^ 2 / 2))
    (hc : c ≠ 0) (i : Fin 3) :
    Module.End.HasEigenvector (Matrix.toLin' (reducedJacobian u H))
      (eigenvalues u c i) (rightEigenbasis u H c hacoustic hc i) := by
  have hcolumn :
      rightEigenbasis u H c hacoustic hc i =
        (rightEigenvectors u H c).col i := by
    rw [coe_rightEigenbasis]
  rw [hcolumn]
  exact reducedJacobian_hasEigenvector u H c hacoustic hc i

/-- Positive acoustic speed strictly orders the three displayed values. -/
theorem eigenvalues_strictMono (u c : ℝ) (hc : 0 < c) :
    StrictMono (eigenvalues u c) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simp [eigenvalues] <;> linarith

/-! ## Specialization to admissible conservative Euler states -/

/-- Positive acoustic speed obtained from the conservative thermodynamic
state. -/
noncomputable def soundSpeed (U : Vec3) : ℝ :=
  Real.sqrt (soundSpeedSquared U)

theorem soundSpeed_pos (U : Vec3) (hU : Admissible U) :
    0 < soundSpeed U := by
  exact Real.sqrt_pos.2 hU.soundSpeedSquared_pos

theorem soundSpeed_sq (U : Vec3) (hU : Admissible U) :
    soundSpeed U ^ 2 = soundSpeedSquared U := by
  exact Real.sq_sqrt hU.soundSpeedSquared_pos.le

/-- The thermodynamic sound speed discharges the algebraic eigenvector
hypothesis. -/
theorem soundSpeed_acousticRelation (U : Vec3) (hU : Admissible U) :
    soundSpeed U ^ 2 =
      ((2 : ℝ) / 5) *
        (specificEnthalpy U - velocity U ^ 2 / 2) := by
  rw [soundSpeed_sq U hU]
  exact soundSpeedSquared_eq_enthalpyGap U hU.density_ne

/-- Characteristic values of an admissible conservative state. -/
noncomputable def characteristicValues (U : Vec3) : Fin 3 → ℝ :=
  eigenvalues (velocity U) (soundSpeed U)

/-- Right-eigenvector matrix of an admissible conservative state. -/
noncomputable def eulerRightEigenvectors (U : Vec3) : Mat3 :=
  rightEigenvectors (velocity U) (specificEnthalpy U) (soundSpeed U)

/-- Diagonal characteristic matrix of an admissible conservative state. -/
noncomputable def characteristicMatrix (U : Vec3) : Mat3 :=
  Matrix.diagonal (characteristicValues U)

/-- Complete matrix eigenrelation for the explicit conservative-coordinate
flux Jacobian. -/
theorem fluxJacobian_mul_eulerRightEigenvectors
    (U : Vec3) (hU : Admissible U) :
    fluxJacobian U * eulerRightEigenvectors U =
      eulerRightEigenvectors U * characteristicMatrix U := by
  rw [fluxJacobian_eq_reduced U hU.density_ne]
  simpa [eulerRightEigenvectors, characteristicMatrix,
    characteristicValues, eigenvalueMatrix] using
    reducedJacobian_mul_rightEigenvectors
      (velocity U) (specificEnthalpy U) (soundSpeed U)
      (soundSpeed_acousticRelation U hU)

theorem fluxJacobian_mulVec_eulerRightEigenvector
    (U : Vec3) (hU : Admissible U) (i : Fin 3) :
    fluxJacobian U *ᵥ (eulerRightEigenvectors U).col i =
      characteristicValues U i • (eulerRightEigenvectors U).col i := by
  apply mulVec_col_of_mul_eq_mul_diagonal
  simpa only [characteristicMatrix] using
    fluxJacobian_mul_eulerRightEigenvectors U hU

/-- Physical determinant identity `det R = 7*c*p/rho`. -/
theorem det_eulerRightEigenvectors
    (U : Vec3) (hrho : density U ≠ 0) :
    (eulerRightEigenvectors U).det =
      7 * soundSpeed U * pressure U / density U := by
  simp only [eulerRightEigenvectors]
  rw [det_rightEigenvectors, specificEnthalpy_gap U hrho]
  ring

theorem det_eulerRightEigenvectors_pos
    (U : Vec3) (hU : Admissible U) :
    0 < (eulerRightEigenvectors U).det := by
  rw [det_eulerRightEigenvectors U hU.density_ne]
  apply div_pos
  · exact mul_pos
      (mul_pos (by norm_num) (soundSpeed_pos U hU)) hU.pressure_pos
  · exact hU.density_pos

theorem det_eulerRightEigenvectors_ne_zero
    (U : Vec3) (hU : Admissible U) :
    (eulerRightEigenvectors U).det ≠ 0 :=
  ne_of_gt (det_eulerRightEigenvectors_pos U hU)

theorem eulerRightEigenvectors_linearIndependent
    (U : Vec3) (hU : Admissible U) :
    LinearIndependent ℝ (eulerRightEigenvectors U).col :=
  Matrix.linearIndependent_cols_of_det_ne_zero
    (det_eulerRightEigenvectors_ne_zero U hU)

/-- Actual eigenbasis for every conservative state with positive density and
pressure. -/
noncomputable def eulerEigenbasis
    (U : Vec3) (hU : Admissible U) : Basis (Fin 3) ℝ Vec3 :=
  basisOfPiSpaceOfLinearIndependent
    (eulerRightEigenvectors_linearIndependent U hU)

@[simp] theorem coe_eulerEigenbasis
    (U : Vec3) (hU : Admissible U) :
    ⇑(eulerEigenbasis U hU) = (eulerRightEigenvectors U).col := by
  simp only [eulerEigenbasis, coe_basisOfPiSpaceOfLinearIndependent]

/-- Admissibility makes the characteristic values strictly ordered. -/
theorem characteristicValues_strictMono
    (U : Vec3) (hU : Admissible U) :
    StrictMono (characteristicValues U) := by
  exact eigenvalues_strictMono (velocity U) (soundSpeed U)
    (soundSpeed_pos U hU)

theorem fluxJacobian_hasEigenvector
    (U : Vec3) (hU : Admissible U) (i : Fin 3) :
    Module.End.HasEigenvector (Matrix.toLin' (fluxJacobian U))
      (characteristicValues U i) ((eulerRightEigenvectors U).col i) := by
  rw [Module.End.hasEigenvector_iff]
  refine ⟨?_, LinearIndependent.ne_zero i
    (eulerRightEigenvectors_linearIndependent U hU)⟩
  rw [Module.End.mem_eigenspace_iff]
  simpa only [Matrix.toLin'_apply] using
    fluxJacobian_mulVec_eulerRightEigenvector U hU i

theorem eulerEigenbasis_hasEigenvector
    (U : Vec3) (hU : Admissible U) (i : Fin 3) :
    Module.End.HasEigenvector (Matrix.toLin' (fluxJacobian U))
      (characteristicValues U i) (eulerEigenbasis U hU i) := by
  have hcolumn :
      eulerEigenbasis U hU i = (eulerRightEigenvectors U).col i := by
    rw [coe_eulerEigenbasis]
  rw [hcolumn]
  exact fluxJacobian_hasEigenvector U hU i

/-- A concise strict-hyperbolicity certificate: three strictly ordered real
eigenvalues with an eigenvector basis spanning all conservative states. -/
theorem exists_strict_complete_eigenbasis
    (U : Vec3) (hU : Admissible U) :
    ∃ b : Basis (Fin 3) ℝ Vec3,
      StrictMono (characteristicValues U) ∧
      ∀ i, Module.End.HasEigenvector (Matrix.toLin' (fluxJacobian U))
        (characteristicValues U i) (b i) := by
  exact ⟨eulerEigenbasis U hU, characteristicValues_strictMono U hU,
    eulerEigenbasis_hasEigenvector U hU⟩

#print axioms reducedJacobian_mul_rightEigenvectors
#print axioms det_rightEigenvectors_eq_five_mul_cube
#print axioms fluxJacobian_mul_eulerRightEigenvectors
#print axioms det_eulerRightEigenvectors_pos
#print axioms exists_strict_complete_eigenbasis

end

end Project.EulerRusanov.RealEigenbasis
