import Project.EulerRusanov.Model
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Conservative-coordinate real Euler model

This module separates the mathematical conservative-coordinate Euler flux
from the primitive-coordinate expression tree used by the executable model.
The distinction matters for the later Jacobian theorem: the standard Euler
eigenvectors describe the derivative with respect to `(rho, momentum, E)`,
not the derivative with respect to `(rho, velocity, pressure)`.

All divisions below are total as Lean real-number operations.  The theorems
that use their physical field interpretation explicitly assume nonzero or
positive density.
-/

namespace Project.EulerRusanov.RealConservative

/-! ## Conservative states and thermodynamic quantities -/

/-- Three conservative coordinates `(rho, momentum, totalEnergy)`. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Density coordinate. -/
def density (U : Vec3) : ℝ := U 0

/-- Momentum-density coordinate. -/
def momentum (U : Vec3) : ℝ := U 1

/-- Total-energy-density coordinate. -/
def totalEnergy (U : Vec3) : ℝ := U 2

/-- Velocity recovered from a conservative state of nonzero density. -/
noncomputable def velocity (U : Vec3) : ℝ :=
  momentum U / density U

/-- Internal-energy density recovered from conservative coordinates. -/
noncomputable def internalEnergy (U : Vec3) : ℝ :=
  totalEnergy U - momentum U ^ 2 / (2 * density U)

/-- Ideal-gas pressure for `gamma = 7 / 5`, hence `gamma - 1 = 2 / 5`. -/
noncomputable def pressure (U : Vec3) : ℝ :=
  ((2 : ℝ) / 5) * internalEnergy U

/-- Specific total enthalpy `(E + p) / rho`.

This is deliberately distinct from `Model.SideBits.enthalpy`, whose decoded
real value represents the density `E + p`. -/
noncomputable def specificEnthalpy (U : Vec3) : ℝ :=
  (totalEnergy U + pressure U) / density U

/-- Squared acoustic speed `gamma * p / rho`. -/
noncomputable def soundSpeedSquared (U : Vec3) : ℝ :=
  Model.gammaReal * pressure U / density U

/-! ## Primitive and structure bridges -/

/-- Independent primitive-to-conservative map for `gamma = 7 / 5`. -/
noncomputable def primitiveToConservative
    (q : Model.PrimitiveReal) : Vec3 :=
  ![q.rho,
    q.rho * q.velocity,
    ((5 : ℝ) / 2) * q.pressure +
      ((1 : ℝ) / 2) * ((q.rho * q.velocity) * q.velocity)]

/-- Coordinate-vector view of the existing conservative-state structure. -/
def conservativeRealVec (U : Model.ConservativeReal) : Vec3 :=
  ![U.density, U.momentum, U.energy]

/-- Coordinate-vector view of the existing physical-flux structure. -/
def fluxRealVec (F : Model.FluxReal) : Vec3 :=
  ![F.mass, F.momentum, F.energy]

@[simp] theorem density_primitiveToConservative (q : Model.PrimitiveReal) :
    density (primitiveToConservative q) = q.rho := by
  rfl

@[simp] theorem momentum_primitiveToConservative (q : Model.PrimitiveReal) :
    momentum (primitiveToConservative q) = q.rho * q.velocity := by
  rfl

@[simp] theorem totalEnergy_primitiveToConservative
    (q : Model.PrimitiveReal) :
    totalEnergy (primitiveToConservative q) =
      ((5 : ℝ) / 2) * q.pressure +
        ((1 : ℝ) / 2) * ((q.rho * q.velocity) * q.velocity) := by
  rfl

/-- The independent vector map is exactly the existing real model's map. -/
theorem primitiveToConservative_eq_model (q : Model.PrimitiveReal) :
    primitiveToConservative q =
      conservativeRealVec (Model.conservativeReal q) := by
  funext i
  fin_cases i <;>
    simp [primitiveToConservative, conservativeRealVec,
      Model.conservativeReal]

theorem velocity_primitiveToConservative
    (q : Model.PrimitiveReal) (hrho : q.rho ≠ 0) :
    velocity (primitiveToConservative q) = q.velocity := by
  simp only [velocity, momentum_primitiveToConservative,
    density_primitiveToConservative]
  apply (div_eq_iff hrho).2
  ring

theorem internalEnergy_primitiveToConservative
    (q : Model.PrimitiveReal) :
    internalEnergy (primitiveToConservative q) =
      ((5 : ℝ) / 2) * q.pressure := by
  simp only [internalEnergy, totalEnergy_primitiveToConservative,
    momentum_primitiveToConservative, density_primitiveToConservative]
  field_simp
  ring

theorem pressure_primitiveToConservative
    (q : Model.PrimitiveReal) :
    pressure (primitiveToConservative q) = q.pressure := by
  rw [pressure, internalEnergy_primitiveToConservative q]
  ring

/-! ## Conservative physical flux -/

/-- Exact Euler flux in conservative coordinates for `gamma = 7 / 5`.

This expanded rational form is the one differentiated by the later Jacobian
module.
-/
noncomputable def conservativeFlux (U : Vec3) : Vec3 :=
  ![momentum U,
    ((4 : ℝ) / 5) * momentum U ^ 2 / density U +
      ((2 : ℝ) / 5) * totalEnergy U,
    ((7 : ℝ) / 5) * totalEnergy U * momentum U / density U -
      ((1 : ℝ) / 5) * momentum U ^ 3 / density U ^ 2]

/-- The expanded conservative flux equals the usual pressure form. -/
theorem conservativeFlux_eq_pressureForm
    (U : Vec3) (hrho : density U ≠ 0) :
    conservativeFlux U =
      ![momentum U,
        momentum U * velocity U + pressure U,
        (totalEnergy U + pressure U) * velocity U] := by
  have h0 : U 0 ≠ 0 := by
    simpa only [density] using hrho
  funext i
  fin_cases i <;>
    simp [conservativeFlux, velocity, pressure, internalEnergy,
      density, momentum, totalEnergy] <;>
    field_simp [h0] <;>
    ring

/-- At a non-vacuum primitive state, the conservative-coordinate flux agrees
exactly with the existing independent primitive-coordinate Euler flux. -/
theorem conservativeFlux_primitiveToConservative
    (q : Model.PrimitiveReal) (hrho : q.rho ≠ 0) :
    conservativeFlux (primitiveToConservative q) =
      fluxRealVec (Model.eulerFluxReal q) := by
  have hrhoU : density (primitiveToConservative q) ≠ 0 := by
    simpa only [density_primitiveToConservative] using hrho
  rw [conservativeFlux_eq_pressureForm _ hrhoU]
  funext i
  fin_cases i <;>
    simp [fluxRealVec, Model.eulerFluxReal,
      velocity_primitiveToConservative q hrho,
      pressure_primitiveToConservative q]

/-! ## Admissibility and eigensystem identities -/

/-- The open Euler admissible set: positive density and pressure. -/
structure Admissible (U : Vec3) : Prop where
  density_pos : 0 < density U
  pressure_pos : 0 < pressure U

theorem pressure_pos_iff_internalEnergy_pos (U : Vec3) :
    0 < pressure U ↔ 0 < internalEnergy U := by
  change 0 < ((2 : ℝ) / 5) * internalEnergy U ↔
    0 < internalEnergy U
  exact mul_pos_iff_of_pos_left (by norm_num)

theorem Admissible.density_ne {U : Vec3} (h : Admissible U) :
    density U ≠ 0 :=
  ne_of_gt h.density_pos

theorem Admissible.internalEnergy_pos {U : Vec3} (h : Admissible U) :
    0 < internalEnergy U :=
  (pressure_pos_iff_internalEnergy_pos U).mp h.pressure_pos

theorem Admissible.soundSpeedSquared_pos
    {U : Vec3} (h : Admissible U) :
    0 < soundSpeedSquared U := by
  apply div_pos
  · exact mul_pos (by norm_num [Model.gammaReal]) h.pressure_pos
  · exact h.density_pos

/-- Positive primitive density and pressure produce an admissible
conservative state. -/
theorem primitiveToConservative_admissible
    (q : Model.PrimitiveReal)
    (hrho : 0 < q.rho) (hpressure : 0 < q.pressure) :
    Admissible (primitiveToConservative q) := by
  refine ⟨?_, ?_⟩
  · simpa only [density_primitiveToConservative] using hrho
  · rw [pressure_primitiveToConservative q]
    exact hpressure

/-- Thermodynamic enthalpy identity used by the characteristic polynomial and
eigenvector calculations. -/
theorem specificEnthalpy_gap
    (U : Vec3) (hrho : density U ≠ 0) :
    specificEnthalpy U - velocity U ^ 2 / 2 =
      ((7 : ℝ) / 2) * pressure U / density U := by
  have h0 : U 0 ≠ 0 := by
    simpa only [density] using hrho
  simp only [specificEnthalpy, velocity, pressure, internalEnergy,
    density, momentum, totalEnergy]
  field_simp [h0]
  ring

/-- For `gamma = 7 / 5`, acoustic speed squared is `2 / 5` times the
enthalpy gap. -/
theorem soundSpeedSquared_eq_enthalpyGap
    (U : Vec3) (hrho : density U ≠ 0) :
    soundSpeedSquared U =
      ((2 : ℝ) / 5) *
        (specificEnthalpy U - velocity U ^ 2 / 2) := by
  rw [specificEnthalpy_gap U hrho]
  simp only [soundSpeedSquared, Model.gammaReal]
  ring

#print axioms conservativeFlux_primitiveToConservative
#print axioms primitiveToConservative_admissible
#print axioms soundSpeedSquared_eq_enthalpyGap

end Project.EulerRusanov.RealConservative
