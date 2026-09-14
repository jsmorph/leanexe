import Project.Euler2DConservative.RealFlux
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Project.Euler2DConservative.RealFlux
open Guard (Vec4 internalEnergy pressure)
open scoped Matrix

noncomputable section

def matrixCLM (A : Mat4) : Vec4 →L[ℝ] Vec4 :=
  LinearMap.toContinuousLinearMap A.mulVecLin

@[simp] theorem matrixCLM_apply (A : Mat4) (V : Vec4) :
    matrixCLM A V = A *ᵥ V := rfl

theorem hasFDerivAt_xFlux (U : Vec4) (hr : U 0 ≠ 0) :
    HasFDerivAt xFlux (matrixCLM (xJacobian U)) U := by
  let coord (i : Fin 4) : Vec4 →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) i
  have hcoord (i : Fin 4) : HasFDerivAt (fun X : Vec4 => X i) (coord i) U :=
    hasFDerivAt_apply i U
  have hv := (hcoord 1).mul ((hasFDerivAt_inv hr).comp U (hcoord 0))
  have hp := ((hcoord 3).sub
    ((((hcoord 1).pow 2).add ((hcoord 2).pow 2)).mul
      ((hasFDerivAt_inv (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hr)).comp U
        ((hcoord 0).const_mul 2)))).const_mul (2/5 : ℝ)
  have h0 := hcoord 1
  have h1 := ((hcoord 1).mul hv).add hp
  have h2 := (hcoord 2).mul hv
  have h3 := ((hcoord 3).add hp).mul hv
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i <;>
    dsimp only [xFlux, velocity, pressure, internalEnergy] <;>
    simp only [div_eq_mul_inv]
  · apply h0.congr_fderiv
    ext dU
    simp [coord, matrixCLM, xJacobian, reducedJacobian,
      dotProduct, Fin.sum_univ_succ]
  all_goals first | apply h1.congr_fderiv | apply h2.congr_fderiv | apply h3.congr_fderiv
  all_goals
    ext dU
    simp [coord, matrixCLM, xJacobian, reducedJacobian, velocity,
      transverseVelocity, enthalpy, pressure, internalEnergy,
      dotProduct, Fin.sum_univ_succ, ContinuousLinearMap.toSpanSingleton_apply]
    field_simp [hr]
    ring

#print axioms hasFDerivAt_xFlux

end
end Project.Euler2DConservative.RealFlux
