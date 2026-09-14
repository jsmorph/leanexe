import Project.Euler2DConservative.Guard
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Project.Euler2DConservative.RealFlux

open Guard (Vec4 internalEnergy pressure Admissible)
open scoped Matrix

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

noncomputable section

def velocity (U : Vec4) : ℝ := U 1 / U 0
def transverseVelocity (U : Vec4) : ℝ := U 2 / U 0
def enthalpy (U : Vec4) : ℝ := (U 3 + pressure U) / U 0

def xFlux (U : Vec4) : Vec4 :=
  ![U 1, U 1 * velocity U + pressure U,
    U 2 * velocity U, (U 3 + pressure U) * velocity U]

def yFlux (U : Vec4) : Vec4 :=
  ![U 2, U 1 * transverseVelocity U,
    U 2 * transverseVelocity U + pressure U,
    (U 3 + pressure U) * transverseVelocity U]

def reducedJacobian (u v H : ℝ) : Mat4 :=
  !![0, 1, 0, 0;
    -(4/5 : ℝ)*u^2 + (1/5 : ℝ)*v^2, (8/5 : ℝ)*u, -(2/5 : ℝ)*v, 2/5;
    -u*v, v, u, 0;
    u*((1/5 : ℝ)*(u^2+v^2)-H), H-(2/5 : ℝ)*u^2,
      -(2/5 : ℝ)*u*v, (7/5 : ℝ)*u]

def xJacobian (U : Vec4) : Mat4 :=
  reducedJacobian (velocity U) (transverseVelocity U) (enthalpy U)

theorem acoustic_identity (U : Vec4) (hr : U 0 ≠ 0) :
    (2/5 : ℝ) * (enthalpy U - (velocity U ^ 2 + transverseVelocity U ^ 2)/2) =
      (7/5 : ℝ) * pressure U / U 0 := by
  unfold enthalpy velocity transverseVelocity pressure internalEnergy
  field_simp
  ring

end
end Project.Euler2DConservative.RealFlux
