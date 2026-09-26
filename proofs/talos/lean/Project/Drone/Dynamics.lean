import Project.Drone.Edges

namespace Project.Drone.Dynamics
open LeanExe.Examples.Drone Arithmetic Edges

noncomputable section

def real (w : UInt64) : ℝ := w.toNat

theorem distance_real (a b : UInt64) : real (distance a b) = |real b-real a| := by
  dsimp [real]
  rw [distance_nat]
  split <;> rename_i h
  · rw [Nat.cast_sub h, abs_of_nonpos (by exact_mod_cast (show (b.toNat:ℤ)-a.toNat ≤ 0 by omega))]
    ring
  · have h' : a.toNat ≤ b.toNat := by omega
    rw [Nat.cast_sub h', abs_of_nonneg (by exact_mod_cast (show (0:ℤ) ≤ (b.toNat:ℤ)-a.toNat by omega))]

theorem total_positive (u v : UInt64) (hu : u.toNat ≤ 20) (hv : v.toNat ≤ 20)
    (ht : u+v ≠ 0) : 0 < real u+real v := by
  have hsum : (u+v).toNat = u.toNat+v.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hn : (u+v).toNat ≠ 0 := fun h => ht (UInt64.toNat_inj.mp h)
  have : 0 < u.toNat+v.toNat := by omega
  dsimp [real]
  exact_mod_cast this

/-- The accepted executable guards imply the three real motion inequalities.
The division here is real division; exact tick representation is proved in
Timing.lean. -/
theorem forward_conditions (r0 r1 z0 z1 u v : UInt64)
    (hz0 : z0.toNat ≤ heightLimit) (hz1 : z1.toNat ≤ heightLimit)
    (hu : u.toNat ≤ 20) (hv : v.toNat ≤ 20)
    (hedge : 0 < edgeTicks r0 r1 z0 z1 u v) (ht : u+v ≠ 0) :
    0 < 200/(real u+real v) ∧
    3*|real z1-real z0| ≤ 40*(200/(real u+real v)) ∧
    6*|real z1-real z0| ≤ 4*(200/(real u+real v))^2 ∧
    |real v^2-real u^2|/200 ≤ 1 := by
  obtain ⟨ha, hr, hvz, _, _⟩ := accepted_guards r0 r1 z0 z1 u v hedge ht
  obtain ⟨_, hu2, hv2, hrate, hacc⟩ :=
    products_nat (distance z0 z1) u v (distance_le z0 z1 hz0 hz1) hu hv
  have hs := total_positive u v hu hv ht
  have hT : 0 < 200/(real u+real v) := div_pos (by norm_num) hs
  have hnrate := UInt64.le_iff_toNat_le.mp hr
  have hnacc := UInt64.le_iff_toNat_le.mp hvz
  rw [hrate] at hnrate
  rw [hacc] at hnacc
  change 3*(distance z0 z1).toNat*(u.toNat+v.toNat) ≤ 8000 at hnrate
  change 6*(distance z0 z1).toNat*(u.toNat+v.toNat)*(u.toNat+v.toNat) ≤ 160000 at hnacc
  have hR : 3*real (distance z0 z1)*(real u+real v) ≤ 8000 := by dsimp [real]; exact_mod_cast hnrate
  have hA : 6*real (distance z0 z1)*(real u+real v)*(real u+real v) ≤ 160000 := by dsimp [real]; exact_mod_cast hnacc
  rw [distance_real] at hR hA
  have hsqU : real (u*u) = real u^2 := by dsimp [real]; rw [hu2]; push_cast; ring
  have hsqV : real (v*v) = real v^2 := by dsimp [real]; rw [hv2]; push_cast; ring
  have hnH : (distance (u*u) (v*v)).toNat ≤ 200 := UInt64.le_iff_toNat_le.mp ha
  have hH : real (distance (u*u) (v*v)) ≤ 200 := by dsimp [real]; exact_mod_cast hnH
  rw [distance_real, hsqU, hsqV] at hH
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hs).mpr
    nlinarith
  · have heq : 4*(200/(real u+real v))^2 = 160000/(real u+real v)^2 := by field_simp; ring
    rw [heq]
    apply (le_div_iff₀ (sq_pos_of_pos hs)).mpr
    nlinarith [hA]
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<200)).mpr
    linarith

/-- Both component speed and acceleration bounds hold on every moving edge. -/
theorem accepted_forward_bounds (r0 r1 z0 z1 u v : UInt64)
    (hz0 : z0.toNat ≤ heightLimit) (hz1 : z1.toNat ≤ heightLimit)
    (hu : u.toNat ≤ 20) (hv : v.toNat ≤ 20)
    (hedge : 0 < edgeTicks r0 r1 z0 z1 u v) (ht : u+v ≠ 0)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let T := 200/(real u+real v)
    (0 ≤ (1-s)*real u+s*real v ∧ (1-s)*real u+s*real v ≤ 20) ∧
    |(real v^2-real u^2)/200| ≤ 1 ∧
    |(real z1-real z0)*(6*s*(1-s))/T| ≤ 20 ∧
    |(real z1-real z0)*(6-12*s)/T^2| ≤ 4 := by
  obtain ⟨hT, hr, ha, hh⟩ := forward_conditions r0 r1 z0 z1 u v hz0 hz1 hu hv hedge ht
  refine ⟨Motion.horizontal_speed_bound (Nat.cast_nonneg _) (by dsimp [real]; exact_mod_cast hu)
    (Nat.cast_nonneg _) (by dsimp [real]; exact_mod_cast hv) hs0 hs1, ?_,
    Motion.vertical_speed_bound hT hr hs0 hs1,
    Motion.vertical_accel_bound hT ha hs0 hs1⟩
  simpa only [abs_div, abs_of_pos (by norm_num : (0:ℝ)<200)] using hh

/-- The actual rest duration meets the continuous component limits. -/
theorem rest_bounds (z0 z1 : UInt64)
    (hz0 : z0.toNat ≤ heightLimit) (hz1 : z1.toNat ≤ heightLimit)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let T := real (restSeconds (distance z0 z1))
    0 < T ∧
    (0 ≤ 100*(6*s*(1-s))/T ∧ 100*(6*s*(1-s))/T ≤ 20) ∧
    |100*(6-12*s)/T^2| ≤ 1 ∧
    |(real z1-real z0)*(6*s*(1-s))/T| ≤ 20 ∧
    |(real z1-real z0)*(6-12*s)/T^2| ≤ 4 := by
  dsimp only
  let T := real (restSeconds (distance z0 z1))
  obtain ⟨ht, hr, ha, _⟩ := restSeconds_bounds (distance z0 z1) (distance_le z0 z1 hz0 hz1)
  have h25 : (25:ℝ) ≤ T := by dsimp [T, real]; exact_mod_cast ht
  have hT : 0 < T := by linarith
  have hrR : 3*real (distance z0 z1) ≤ 40*T := by dsimp [T, real]; exact_mod_cast hr
  have haR : 3*real (distance z0 z1) ≤ 2*T^2 := by dsimp [T, real]; exact_mod_cast ha
  rw [distance_real] at hrR haR
  obtain ⟨hf0, hf1⟩ := Motion.vertical_rate_factor hs0 hs1
  refine ⟨hT, ⟨by positivity, ?_⟩, ?_, Motion.vertical_speed_bound hT hrR hs0 hs1,
    Motion.vertical_accel_bound hT (by linarith) hs0 hs1⟩
  · apply (div_le_iff₀ hT).mpr
    nlinarith
  · rw [abs_div, abs_of_nonneg (sq_nonneg T), abs_mul]
    norm_num
    apply (div_le_iff₀ (sq_pos_of_pos hT)).mpr
    have := Motion.vertical_accel_factor hs0 hs1
    nlinarith

#print axioms accepted_forward_bounds
#print axioms rest_bounds
end
end Project.Drone.Dynamics
