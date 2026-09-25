import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Continuous safety of the drone's motion primitives. These theorems are
mathematical: the separate word-arithmetic and execution layers must establish
their hypotheses for the actual program output. -/
namespace Project.Drone.Motion

noncomputable section

def smooth (s : ℝ) : ℝ := 3*s^2-2*s^3

def altitude (z0 z1 s : ℝ) : ℝ := z0+(z1-z0)*smooth s

def fraction (u v s : ℝ) : ℝ := (2*u*s+(v-u)*s^2)/(u+v)

def floor (r0 r1 q : ℝ) : ℝ := r0+(r1-r0)*q

def bernstein (b0 b1 b2 b3 s : ℝ) : ℝ :=
  b0*(1-s)^3+3*b1*s*(1-s)^2+3*b2*s^2*(1-s)+b3*s^3

theorem smooth_bounds {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    0 ≤ smooth s ∧ smooth s ≤ 1 := by
  have hleft : 0 ≤ s^2*(3-2*s) := mul_nonneg (sq_nonneg s) (by linarith)
  have hright : 0 ≤ (1-s)^2*(1+2*s) :=
    mul_nonneg (sq_nonneg (1-s)) (by linarith)
  constructor <;> dsimp [smooth] <;> nlinarith

theorem bernstein_nonneg {b0 b1 b2 b3 s : ℝ}
    (h0 : 0 ≤ b0) (h1 : 0 ≤ b1) (h2 : 0 ≤ b2) (h3 : 0 ≤ b3)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ bernstein b0 b1 b2 b3 s := by
  have ht : 0 ≤ 1-s := by linarith
  unfold bernstein
  positivity

theorem clearance_identity (r0 r1 z0 z1 u v s : ℝ) (h : u+v ≠ 0) :
    altitude z0 z1 s - floor r0 r1 (fraction u v s) =
      bernstein (z0-r0) (z0-r0-2*u*(r1-r0)/(3*(u+v)))
        (z1-r1+2*v*(r1-r0)/(3*(u+v))) (z1-r1) s := by
  unfold altitude floor fraction bernstein smooth
  field_simp
  ring

theorem forward_clearance {r0 r1 z0 z1 u v s : ℝ}
    (huv : 0 < u+v) (hstart : r0 ≤ z0) (hend : r1 ≤ z1)
    (hb1 : 2*u*(r1-r0) ≤ 3*(u+v)*(z0-r0))
    (hb2 : -2*v*(r1-r0) ≤ 3*(u+v)*(z1-r1))
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    floor r0 r1 (fraction u v s) ≤ altitude z0 z1 s := by
  have hden : 0 < 3*(u+v) := by positivity
  have b1 : 0 ≤ z0-r0-2*u*(r1-r0)/(3*(u+v)) := by
    have := (div_le_iff₀ hden).mpr (by nlinarith [hb1] :
      2*u*(r1-r0) ≤ (z0-r0)*(3*(u+v)))
    linarith
  have b2 : 0 ≤ z1-r1+2*v*(r1-r0)/(3*(u+v)) := by
    have := (le_div_iff₀ hden).mpr (by nlinarith [hb2] :
      (-(z1-r1))*(3*(u+v)) ≤ 2*v*(r1-r0))
    linarith
  have := bernstein_nonneg (sub_nonneg.mpr hstart) b1 b2
    (sub_nonneg.mpr hend) hs0 hs1
  rw [← clearance_identity r0 r1 z0 z1 u v s (ne_of_gt huv)] at this
  linarith

theorem rest_clearance {r0 r1 z0 z1 s : ℝ}
    (hstart : r0 ≤ z0) (hend : r1 ≤ z1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    floor r0 r1 (smooth s) ≤ altitude z0 z1 s := by
  obtain ⟨hp0, hp1⟩ := smooth_bounds hs0 hs1
  have ha := mul_nonneg (sub_nonneg.mpr hstart) (sub_nonneg.mpr hp1)
  have hb := mul_nonneg (sub_nonneg.mpr hend) hp0
  dsimp [floor, altitude]
  nlinarith

theorem vertical_rate_factor {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ 6*s*(1-s) ∧ 6*s*(1-s) ≤ 3/2 := by
  constructor
  · positivity
  · nlinarith [sq_nonneg (2*s-1)]

theorem vertical_accel_factor {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |6-12*s| ≤ 6 := by
  apply abs_le.mpr
  constructor <;> linarith

theorem vertical_speed_bound {dz T s : ℝ} (hT : 0 < T)
    (hrate : 3*|dz| ≤ 40*T) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |dz*(6*s*(1-s))/T| ≤ 20 := by
  obtain ⟨hf0, hf1⟩ := vertical_rate_factor hs0 hs1
  rw [abs_div, abs_of_pos hT, abs_mul, abs_of_nonneg hf0]
  apply (div_le_iff₀ hT).mpr
  have := mul_le_mul_of_nonneg_left hf1 (abs_nonneg dz)
  nlinarith

theorem vertical_accel_bound {dz T s : ℝ} (hT : 0 < T)
    (haccel : 6*|dz| ≤ 4*T^2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |dz*(6-12*s)/T^2| ≤ 4 := by
  rw [abs_div, abs_of_nonneg (sq_nonneg T), abs_mul]
  apply (div_le_iff₀ (sq_pos_of_pos hT)).mpr
  have := mul_le_mul_of_nonneg_left (vertical_accel_factor hs0 hs1) (abs_nonneg dz)
  nlinarith

theorem horizontal_speed_bound {u v s : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 20) (hv0 : 0 ≤ v) (hv1 : v ≤ 20)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ (1-s)*u+s*v ∧ (1-s)*u+s*v ≤ 20 := by
  have hs : 0 ≤ 1-s := by linarith
  constructor
  · positivity
  · have hleft := mul_le_mul_of_nonneg_left hu1 hs
    have hright := mul_le_mul_of_nonneg_left hv1 hs0
    nlinarith

theorem endpoint_values (z0 z1 : ℝ) :
    altitude z0 z1 0 = z0 ∧ altitude z0 z1 1 = z1 := by
  constructor <;> dsimp [altitude, smooth] <;> ring

theorem endpoint_vertical_velocity (dz T : ℝ) :
    dz*(6*(0:ℝ)*(1-0))/T = 0 ∧ dz*(6*(1:ℝ)*(1-1))/T = 0 := by
  simp

#print axioms forward_clearance
#print axioms rest_clearance
#print axioms vertical_speed_bound
#print axioms vertical_accel_bound
end
end Project.Drone.Motion
