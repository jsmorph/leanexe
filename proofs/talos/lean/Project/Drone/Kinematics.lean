import Project.Drone.Dynamics
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace Project.Drone.Kinematics
open Motion
noncomputable section

def verticalPosition (z0 z1 T t : ℝ) : ℝ := altitude z0 z1 (t/T)
def verticalVelocity (dz T t : ℝ) : ℝ := dz*(6*(t/T)*(1-t/T))/T
def verticalAcceleration (dz T t : ℝ) : ℝ := dz*(6-12*(t/T))/T^2

theorem smooth_derivative (s : ℝ) : HasDerivAt smooth (6*s*(1-s)) s := by
  convert ((hasDerivAt_pow 2 s).const_mul 3).sub ((hasDerivAt_pow 3 s).const_mul 2) using 1 <;> try rfl
  all_goals (try simp only [smooth]) <;> ring

theorem vertical_derivative (z0 z1 T t : ℝ) :
    HasDerivAt (verticalPosition z0 z1 T) (verticalVelocity (z1-z0) T t) t := by
  have h := ((smooth_derivative (t/T)).comp t ((hasDerivAt_id t).div_const T)).const_mul (z1-z0)
  convert h.const_add z0 using 1 <;> try rfl
  all_goals (try simp only [verticalPosition, verticalVelocity, altitude, Function.comp_apply, id_eq]) <;> ring

theorem vertical_second_derivative (dz T t : ℝ) :
    HasDerivAt (verticalVelocity dz T) (verticalAcceleration dz T t) t := by
  have h := (hasDerivAt_id t).div_const T
  have hv := (((h.const_mul 6).mul (h.const_sub 1)).const_mul dz).div_const T
  convert hv using 1 <;> try rfl
  all_goals (try simp only [verticalVelocity, verticalAcceleration, id_eq]) <;> ring

def forwardPosition (x0 u v t : ℝ) : ℝ :=
  x0+100*fraction u v (t/(200/(u+v)))
def forwardVelocity (u v t : ℝ) : ℝ := (1-t/(200/(u+v)))*u+(t/(200/(u+v)))*v

theorem fraction_derivative (u v s : ℝ) :
    HasDerivAt (fraction u v) ((2*u+2*(v-u)*s)/(u+v)) s := by
  convert (((hasDerivAt_id s).const_mul (2*u)).add
    ((hasDerivAt_pow 2 s).const_mul (v-u))).div_const (u+v) using 1 <;> try rfl
  all_goals
    (try simp only [fraction, id_eq]) <;> ring

theorem forward_derivative (x0 u v t : ℝ) (h : u+v ≠ 0) :
    HasDerivAt (forwardPosition x0 u v) (forwardVelocity u v t) t := by
  have hd := ((fraction_derivative u v (t/(200/(u+v)))).comp t
    ((hasDerivAt_id t).div_const (200/(u+v)))).const_mul 100
  convert hd.const_add x0 using 1 <;> try rfl
  all_goals
    (try simp only [forwardPosition, forwardVelocity, Function.comp_apply, id_eq]) <;>
    (try field_simp) <;> ring

theorem forward_second_derivative (u v t : ℝ) :
    HasDerivAt (forwardVelocity u v) ((v^2-u^2)/200) t := by
  have h := (hasDerivAt_id t).div_const (200/(u+v))
  convert (h.const_sub 1).mul_const u |>.add (h.mul_const v) using 1 <;> try rfl
  all_goals
    (try simp only [forwardVelocity, id_eq, one_div_div]) <;> ring

def restPosition (x0 T t : ℝ) : ℝ := x0+100*smooth (t/T)
def restVelocity (T t : ℝ) : ℝ := 100*(6*(t/T)*(1-t/T))/T

theorem rest_derivative (x0 T t : ℝ) :
    HasDerivAt (restPosition x0 T) (restVelocity T t) t := by
  have h := ((smooth_derivative (t/T)).comp t ((hasDerivAt_id t).div_const T)).const_mul 100
  convert h.const_add x0 using 1 <;> try rfl
  all_goals (try simp only [restPosition, restVelocity, Function.comp_apply, id_eq]) <;> ring

theorem rest_second_derivative (T t : ℝ) :
    HasDerivAt (restVelocity T) (100*(6-12*(t/T))/T^2) t :=
  vertical_second_derivative 100 T t

/-- The horizontal progress remains within the segment. -/
theorem fraction_bounds (u v s : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ht : 0 < u+v) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ fraction u v s ∧ fraction u v s ≤ 1 := by
  have hsm : 0 ≤ 1-s := by linarith
  have hsm2 : 0 ≤ 2-s := by linarith
  have h0 : 0 ≤ u*s*(2-s)+v*s^2 := by positivity
  have h1 : 0 ≤ u*(1-s)^2+v*(1-s)*(1+s) := by positivity
  dsimp [fraction]
  constructor
  · exact div_nonneg (by nlinarith) (le_of_lt ht)
  · apply (div_le_iff₀ ht).mpr
    nlinarith

/-- Each moving segment starts and ends with its specified horizontal state. -/
theorem forward_endpoints (x0 u v : ℝ) (h : u+v ≠ 0) :
    forwardPosition x0 u v 0 = x0 ∧
    forwardPosition x0 u v (200/(u+v)) = x0+100 ∧
    forwardVelocity u v 0 = u ∧
    forwardVelocity u v (200/(u+v)) = v := by
  have hT : 200/(u+v) ≠ 0 := div_ne_zero (by norm_num) h
  simp [forwardPosition, forwardVelocity, fraction, hT]
  field_simp
  ring

/-- Cubic segments agree in altitude and vertical velocity at shared nodes. -/
theorem vertical_endpoints (z0 z1 T : ℝ) (hT : T ≠ 0) :
    verticalPosition z0 z1 T 0 = z0 ∧ verticalPosition z0 z1 T T = z1 ∧
    verticalVelocity (z1-z0) T 0 = 0 ∧ verticalVelocity (z1-z0) T T = 0 := by
  simp [verticalPosition, verticalVelocity, altitude, smooth, hT]
  ring

#print axioms vertical_derivative
#print axioms vertical_second_derivative
#print axioms forward_derivative
#print axioms forward_second_derivative
end
end Project.Drone.Kinematics
