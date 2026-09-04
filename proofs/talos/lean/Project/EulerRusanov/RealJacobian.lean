import Project.EulerRusanov.RealMatrices
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The conservative Euler flux Jacobian

This module proves that `RealMatrices.fluxJacobian` is the Fréchet derivative
of the exact-real Euler flux written in conservative coordinates
`U = (rho, momentum, totalEnergy)`.  The hypothesis `rho != 0` is exactly the
non-vacuum condition needed to differentiate the reciprocal density.

The proof first assembles the three scalar derivatives as rows of a continuous
linear map.  A separate algebraic lemma identifies that proof-oriented map
with multiplication by the displayed Jacobian matrix.  Thus the public result
is about the conservative-coordinate matrix, not the existing
primitive-coordinate executable helper.
-/

namespace Project.EulerRusanov.RealJacobian

open Project.EulerRusanov.RealConservative
open Project.EulerRusanov.RealMatrices
open scoped Matrix

noncomputable section

/-- The continuous linear map represented by the conservative flux Jacobian. -/
def jacobianCLM (U : Vec3) : Vec3 →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap ((fluxJacobian U).mulVecLin)

@[simp]
theorem jacobianCLM_apply (U dU : Vec3) :
    jacobianCLM U dU = fluxJacobian U *ᵥ dU := by
  rfl

/-- Continuous projection onto one conservative coordinate. -/
private def coordinate (i : Fin 3) : Vec3 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) i

/-- A three-entry row acting on conservative perturbations. -/
private def rowCLM (a b c : ℝ) : Vec3 →L[ℝ] ℝ :=
  a • coordinate 0 + b • coordinate 1 + c • coordinate 2

/-- An inverse-normal-form presentation of the conservative flux.  This has
the same value as `conservativeFlux`, but its syntax follows the reciprocal
and multiplication rules used in the derivative construction below. -/
private def differentiableFlux (U : Vec3) : Vec3 :=
  let rho := density U
  let m := momentum U
  let E := totalEnergy U
  ![
    m,
    (4 / 5 : ℝ) * (m ^ 2 * rho⁻¹) + (2 / 5 : ℝ) * E,
    (7 / 5 : ℝ) * ((E * m) * rho⁻¹) -
      (1 / 5 : ℝ) * (m ^ 3 * (rho⁻¹) ^ 2)
  ]

private theorem differentiableFlux_eq_conservativeFlux :
    differentiableFlux = conservativeFlux := by
  funext U
  ext i
  fin_cases i <;>
    simp [differentiableFlux, conservativeFlux, density, momentum,
      totalEnergy, div_eq_mul_inv, inv_pow] <;>
    ring

/-- The Jacobian assembled row by row.  This form matches the componentwise
calculus rules directly; `rowJacobian_eq_jacobianCLM` connects it to the
matrix-backed public definition. -/
private def rowJacobian (U : Vec3) : Vec3 →L[ℝ] Vec3 :=
  let rho := density U
  let m := momentum U
  let E := totalEnergy U
  ContinuousLinearMap.pi ![
    rowCLM 0 1 0,
    rowCLM
      (-(4 / 5 : ℝ) * m ^ 2 / rho ^ 2)
      ((8 / 5 : ℝ) * m / rho)
      (2 / 5),
    rowCLM
      (-(7 / 5 : ℝ) * E * m / rho ^ 2 +
        (2 / 5 : ℝ) * m ^ 3 / rho ^ 3)
      ((7 / 5 : ℝ) * E / rho -
        (3 / 5 : ℝ) * m ^ 2 / rho ^ 2)
      ((7 / 5 : ℝ) * m / rho)
  ]

private theorem rowJacobian_eq_jacobianCLM (U : Vec3) :
    rowJacobian U = jacobianCLM U := by
  apply ContinuousLinearMap.ext
  intro dU
  funext i
  fin_cases i <;>
    simp [rowJacobian, rowCLM, coordinate, jacobianCLM, fluxJacobian,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- The displayed conservative Euler matrix is the Fréchet derivative of the
conservative flux at every non-vacuum state. -/
theorem hasFDerivAt_conservativeFlux (U : Vec3)
    (hrho : density U ≠ 0) :
    HasFDerivAt conservativeFlux (jacobianCLM U) U := by
  have hrhoCoord :
      HasFDerivAt (fun X : Vec3 => density X) (coordinate 0) U := by
    simpa [density, coordinate] using
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) U)
  have hmCoord :
      HasFDerivAt (fun X : Vec3 => momentum X) (coordinate 1) U := by
    simpa [momentum, coordinate] using
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) U)
  have hECoord :
      HasFDerivAt (fun X : Vec3 => totalEnergy X) (coordinate 2) U := by
    simpa [totalEnergy, coordinate] using
      (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) U)
  have hrhoInv := (hasFDerivAt_inv hrho).comp U hrhoCoord

  have hmass :
      HasFDerivAt (fun X : Vec3 => momentum X) (rowCLM 0 1 0) U := by
    apply hmCoord.congr_fderiv
    apply ContinuousLinearMap.ext
    intro dU
    simp [rowCLM, coordinate]

  have hmomentumRaw :=
    (((hmCoord.pow 2).mul hrhoInv).const_mul (4 / 5 : ℝ)).add
      (hECoord.const_mul (2 / 5 : ℝ))
  have hmomentum :
      HasFDerivAt
        (fun X : Vec3 =>
          (4 / 5 : ℝ) *
              (momentum X ^ 2 * (density X)⁻¹) +
            (2 / 5 : ℝ) * totalEnergy X)
        (rowCLM
          (-(4 / 5 : ℝ) * momentum U ^ 2 / density U ^ 2)
          ((8 / 5 : ℝ) * momentum U / density U)
          (2 / 5)) U := by
    apply hmomentumRaw.congr_fderiv
    apply ContinuousLinearMap.ext
    intro dU
    simp [rowCLM, coordinate,
      ContinuousLinearMap.toSpanSingleton_apply]
    field_simp [hrho]
    ring

  have henergyRaw :=
    ((((hECoord.mul hmCoord).mul hrhoInv).const_mul (7 / 5 : ℝ)).sub
      (((hmCoord.pow 3).mul (hrhoInv.pow 2)).const_mul (1 / 5 : ℝ)))
  have henergy :
      HasFDerivAt
        (fun X : Vec3 =>
          (7 / 5 : ℝ) *
              ((totalEnergy X * momentum X) * (density X)⁻¹) -
            (1 / 5 : ℝ) *
              (momentum X ^ 3 * ((density X)⁻¹) ^ 2))
        (rowCLM
          (-(7 / 5 : ℝ) * totalEnergy U * momentum U / density U ^ 2 +
            (2 / 5 : ℝ) * momentum U ^ 3 / density U ^ 3)
          ((7 / 5 : ℝ) * totalEnergy U / density U -
            (3 / 5 : ℝ) * momentum U ^ 2 / density U ^ 2)
          ((7 / 5 : ℝ) * momentum U / density U)) U := by
    apply henergyRaw.congr_fderiv
    apply ContinuousLinearMap.ext
    intro dU
    simp [rowCLM, coordinate,
      ContinuousLinearMap.toSpanSingleton_apply]
    field_simp [hrho]
    ring

  have hrows : HasFDerivAt differentiableFlux (rowJacobian U) U := by
    rw [hasFDerivAt_pi']
    intro i
    fin_cases i
    · simpa [differentiableFlux, rowJacobian] using hmass
    · simpa [differentiableFlux, rowJacobian] using hmomentum
    · simpa [differentiableFlux, rowJacobian] using henergy

  simpa only [differentiableFlux_eq_conservativeFlux] using
    hrows.congr_fderiv (rowJacobian_eq_jacobianCLM U)

/-- The Fréchet derivative itself is the matrix-backed Jacobian map away from
vacuum. -/
theorem fderiv_conservativeFlux (U : Vec3) (hrho : density U ≠ 0) :
    fderiv ℝ conservativeFlux U = jacobianCLM U :=
  (hasFDerivAt_conservativeFlux U hrho).fderiv

/-- Pointwise action of the Fréchet derivative is ordinary Jacobian--vector
multiplication. -/
theorem fderiv_conservativeFlux_apply (U dU : Vec3)
    (hrho : density U ≠ 0) :
    fderiv ℝ conservativeFlux U dU = fluxJacobian U *ᵥ dU := by
  rw [fderiv_conservativeFlux U hrho]
  exact jacobianCLM_apply U dU

#print axioms hasFDerivAt_conservativeFlux
#print axioms fderiv_conservativeFlux
#print axioms fderiv_conservativeFlux_apply

end

end Project.EulerRusanov.RealJacobian
