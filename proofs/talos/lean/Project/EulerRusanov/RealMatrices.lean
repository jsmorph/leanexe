import Project.EulerRusanov.RealConservative
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Conservative Euler matrices

This module states the one-dimensional ideal-gas Euler flux Jacobian in
conservative coordinates `U = (rho, momentum, totalEnergy)`.  It also records
the equivalent denominator-free form parameterized by velocity and specific
total enthalpy.  The latter is the form used by the characteristic polynomial
and eigenbasis calculations.

The derivative theorem identifying `fluxJacobian` as the Fréchet derivative of
`RealConservative.conservativeFlux` is kept in the separate `RealJacobian`
module.  In particular, this matrix is not the derivative of the existing
primitive-coordinate executable helper.
-/

namespace Project.EulerRusanov.RealMatrices

open Project.EulerRusanov.RealConservative

/-- Three-by-three real matrices acting on conservative Euler states. -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- The explicit conservative-coordinate Jacobian of the physical Euler flux
for `gamma = 7 / 5`.

The coordinates are density `rho`, momentum `m`, and total-energy density `E`.
The separate derivative module proves that this displayed matrix is the
Fréchet derivative wherever `rho != 0`. -/
noncomputable def fluxJacobian (U : Vec3) : Mat3 :=
  let rho := density U
  let m := momentum U
  let E := totalEnergy U
  !![
    0, 1, 0;
    -(4 / 5 : ℝ) * m ^ 2 / rho ^ 2,
      (8 / 5 : ℝ) * m / rho,
      2 / 5;
    -(7 / 5 : ℝ) * E * m / rho ^ 2 +
        (2 / 5 : ℝ) * m ^ 3 / rho ^ 3,
      (7 / 5 : ℝ) * E / rho -
        (3 / 5 : ℝ) * m ^ 2 / rho ^ 2,
      (7 / 5 : ℝ) * m / rho
  ]

/-- The same Jacobian expressed using velocity `u` and specific total
enthalpy `H`.  This polynomial form isolates the only thermodynamic relation
needed by the eigenvector calculation. -/
noncomputable def reducedJacobian (u H : ℝ) : Mat3 :=
  !![
    0, 1, 0;
    -(4 / 5 : ℝ) * u ^ 2,
      (8 / 5 : ℝ) * u,
      2 / 5;
    -u * H + (1 / 5 : ℝ) * u ^ 3,
      H - (2 / 5 : ℝ) * u ^ 2,
      (7 / 5 : ℝ) * u
  ]

/-- Away from vacuum, the explicit conservative Jacobian agrees with its
velocity--enthalpy form. -/
theorem fluxJacobian_eq_reduced (U : Vec3) (hrho : density U ≠ 0) :
    fluxJacobian U =
      reducedJacobian (velocity U) (specificEnthalpy U) := by
  have h0 : U 0 ≠ 0 := by
    simpa only [density] using hrho
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fluxJacobian, reducedJacobian, velocity, specificEnthalpy,
      pressure, internalEnergy, density, momentum, totalEnergy] <;>
    field_simp [h0] <;>
    ring

#print axioms fluxJacobian_eq_reduced

end Project.EulerRusanov.RealMatrices
