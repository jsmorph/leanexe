import Project.Drone.Arithmetic
import Project.Drone.Motion

namespace Project.Drone.Edges
open LeanExe.Examples.Drone Arithmetic

/-- A successful moving edge passes every guard in the executable. -/
theorem accepted_guards (r0 r1 z0 z1 u v : UInt64)
    (h : 0 < edgeTicks r0 r1 z0 z1 u v) (ht : u+v ≠ 0) :
    distance (u*u) (v*v) ≤ 200 ∧
    3*distance z0 z1*(u+v) ≤ 8000 ∧
    6*distance z0 z1*(u+v)*(u+v) ≤ 160000 ∧
    (r0 ≤ r1 → 2*u*(r1-r0) ≤ 3*(u+v)*(z0-r0)) ∧
    (r1 < r0 → 2*v*(r0-r1) ≤ 3*(u+v)*(z1-r1)) := by
  simp only [edgeTicks, Id.run, pure, BEq.beq, decide_eq_true_eq] at h
  split at h
  · contradiction
  · split at h
    · simp at h
    · rename_i ha
      split at h
      · simp at h
      · rename_i hv
        split at h
        · simp at h
        · rename_i hz
          split at h
          · rename_i hr
            split at h
            · simp at h
            · rename_i hc
              simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
              omega
          · rename_i hr
            split at h
            · simp at h
            · rename_i hc
              simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
              omega

private theorem mul_nat (a b : UInt64) (h : a.toNat*b.toNat < 18446744073709551616) :
    (a*b).toNat = a.toNat*b.toNat := by
  rw [UInt64.toNat_mul]
  exact Nat.mod_eq_of_lt h

private theorem add_nat (a b : UInt64) (h : a.toNat+b.toNat < 18446744073709551616) :
    (a+b).toNat = a.toNat+b.toNat := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt h

/-- No modular wrap occurs in any moving-edge maneuverability product. -/
theorem products_nat (d u v : UInt64) (hd : d.toNat ≤ heightLimit)
    (hu : u.toNat ≤ 20) (hv : v.toNat ≤ 20) :
    (u+v).toNat = u.toNat+v.toNat ∧
    (u*u).toNat = u.toNat*u.toNat ∧
    (v*v).toNat = v.toNat*v.toNat ∧
    (3*d*(u+v)).toNat = 3*d.toNat*(u.toNat+v.toNat) ∧
    (6*d*(u+v)*(u+v)).toNat = 6*d.toNat*(u.toNat+v.toNat)*(u.toNat+v.toNat) := by
  have ht := add_nat u v (by omega)
  have hu2 := mul_nat u u (by nlinarith)
  have hv2 := mul_nat v v (by nlinarith)
  have hd' : d.toNat ≤ 1000300 := hd
  have h3 : (3*d).toNat = 3*d.toNat := by
    apply mul_nat; change 3*d.toNat < 18446744073709551616; omega
  have h6 : (6*d).toNat = 6*d.toNat := by
    apply mul_nat; change 6*d.toNat < 18446744073709551616; omega
  have h3t : (3*d*(u+v)).toNat = 3*d.toNat*(u.toNat+v.toNat) := by
    rw [mul_nat, h3, ht]
    rw [h3, ht]
    nlinarith
  have h6t : (6*d*(u+v)).toNat = 6*d.toNat*(u.toNat+v.toNat) := by
    rw [mul_nat, h6, ht]
    rw [h6, ht]
    nlinarith
  have h6tt : (6*d*(u+v)*(u+v)).toNat =
      6*d.toNat*(u.toNat+v.toNat)*(u.toNat+v.toNat) := by
    rw [mul_nat, h6t, ht]
    rw [h6t, ht]
    have hp : 6*d.toNat*(u.toNat+v.toNat) ≤ 240072000 := by nlinarith
    nlinarith
  exact ⟨ht, hu2, hv2, h3t, h6tt⟩

/-- No modular wrap occurs in the Bernstein clearance products. -/
theorem clearance_products (r z u v delta : UInt64)
    (hrz : r ≤ z) (hz : z.toNat ≤ heightLimit)
    (hu : u.toNat ≤ 20) (hv : v.toNat ≤ 20) (hd : delta.toNat ≤ heightLimit) :
    (3*(u+v)*(z-r)).toNat = 3*(u.toNat+v.toNat)*(z.toNat-r.toNat) ∧
    (2*u*delta).toNat = 2*u.toNat*delta.toNat := by
  have ht := add_nat u v (by omega)
  have h3t : (3*(u+v)).toNat = 3*(u.toNat+v.toNat) := by
    rw [mul_nat, ht]
    · rfl
    rw [ht]
    change 3*(u.toNat+v.toNat) < 18446744073709551616
    omega
  have h2 : (2*u).toNat = 2*u.toNat := by
    apply mul_nat; change 2*u.toNat < 18446744073709551616; omega
  have hsub := UInt64.toNat_sub_of_le z r hrz
  have hz' : z.toNat ≤ 1000300 := hz
  have hd' : delta.toNat ≤ 1000300 := hd
  constructor
  · rw [mul_nat, h3t, hsub]
    rw [h3t, hsub]
    have : z.toNat-r.toNat ≤ 1000300 := by omega
    nlinarith
  · rw [mul_nat, h2]
    rw [h2]
    nlinarith

/-- Continuous clearance for an accepted moving edge, connected to the actual
UInt64 guards, including their no-overflow obligations. -/
theorem accepted_forward_clearance (r0 r1 z0 z1 u v : UInt64)
    (hz0 : z0.toNat ≤ heightLimit) (hz1 : z1.toNat ≤ heightLimit)
    (hr0 : r0 ≤ z0) (hr1 : r1 ≤ z1)
    (hu : u.toNat ≤ 20) (hv : v.toNat ≤ 20)
    (hedge : 0 < edgeTicks r0 r1 z0 z1 u v) (ht : u+v ≠ 0)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Motion.floor r0.toNat r1.toNat (Motion.fraction u.toNat v.toNat s) ≤
      Motion.altitude z0.toNat z1.toNat s := by
  obtain ⟨_, _, _, hup, hdown⟩ := accepted_guards r0 r1 z0 z1 u v hedge ht
  have hr0n := (UInt64.le_iff_toNat_le).mp hr0
  have hr1n := (UInt64.le_iff_toNat_le).mp hr1
  have hr0R : (r0.toNat : ℝ) ≤ z0.toNat := by exact_mod_cast hr0n
  have hr1R : (r1.toNat : ℝ) ≤ z1.toNat := by exact_mod_cast hr1n
  have huv : 0 < (u.toNat : ℝ)+v.toNat := by
    have heq := add_nat u v (by omega)
    have hne : (u+v).toNat ≠ 0 := by
      intro hz
      apply ht
      exact UInt64.toNat_inj.mp hz
    have hn : 0 < u.toNat+v.toNat := by omega
    exact_mod_cast hn
  apply Motion.forward_clearance huv hr0R hr1R _ _ hs0 hs1
  all_goals
    by_cases hr : r0 ≤ r1
    · have hd := UInt64.toNat_sub_of_le r1 r0 hr
      have hrn := (UInt64.le_iff_toNat_le).mp hr
      have hdelta : (r1-r0).toNat ≤ heightLimit := by rw [hd]; omega
      obtain ⟨ha, hb⟩ := clearance_products r0 z0 u v (r1-r0) hr0 hz0 hu hv hdelta
      have h := (UInt64.le_iff_toNat_le).mp (hup hr)
      rw [ha, hb, hd] at h
      have hR : (2:ℝ)*u.toNat*((r1.toNat-r0.toNat:Nat):ℝ) ≤
          3*(u.toNat+v.toNat)*((z0.toNat-r0.toNat:Nat):ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub hrn, Nat.cast_sub hr0n] at hR
      have hdr : (r0.toNat:ℝ) ≤ r1.toNat := by exact_mod_cast hrn
      have hvR : (0:ℝ) ≤ v.toNat := Nat.cast_nonneg _
      first | exact hR | nlinarith [mul_nonneg hvR (sub_nonneg.mpr hdr), mul_nonneg (le_of_lt huv) (sub_nonneg.mpr hr1R)]
    · have hr' : r1 < r0 := by simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *; omega
      have hrle : r1 ≤ r0 := by simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *; omega
      have hd := UInt64.toNat_sub_of_le r0 r1 hrle
      have hrn := (UInt64.le_iff_toNat_le).mp hrle
      have hdelta : (r0-r1).toNat ≤ heightLimit := by rw [hd]; omega
      obtain ⟨ha, hb⟩ := clearance_products r1 z1 v u (r0-r1) hr1 hz1 hv hu hdelta
      have h := (UInt64.le_iff_toNat_le).mp (hdown hr')
      rw [UInt64.add_comm v u] at ha
      rw [ha, hb, hd] at h
      have hR : (2:ℝ)*v.toNat*((r0.toNat-r1.toNat:Nat):ℝ) ≤
          3*(v.toNat+u.toNat)*((z1.toNat-r1.toNat:Nat):ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub hrn, Nat.cast_sub hr1n] at hR
      have hdr : (r1.toNat:ℝ) ≤ r0.toNat := by exact_mod_cast hrn
      have huR : (0:ℝ) ≤ u.toNat := Nat.cast_nonneg _
      nlinarith [mul_nonneg huR (sub_nonneg.mpr hdr), mul_nonneg (le_of_lt huv) (sub_nonneg.mpr hr0R)]

/-- Every accepted edge between the planner's bounded states clears the entire
interpolated floor, including the rest-to-rest case. This is a theorem about
`edgeTicks` itself; `Safety.compute_segment_clearance` transports it to every
segment of the public returned array. -/
theorem state_edge_clearance (r0 r1 : UInt64) (source target : Nat)
    (hr0 : r0.toNat ≤ 1000100) (hr1 : r1.toNat ≤ 1000100)
    (hsource : source < stateCount) (htarget : target < stateCount)
    (hedge : 0 < edgeTicks r0 r1 (altitude r0 source) (altitude r1 target)
      (speed source) (speed target))
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Motion.floor r0.toNat r1.toNat
      (if speed source + speed target = 0 then Motion.smooth s
       else Motion.fraction (speed source).toNat (speed target).toNat s) ≤
      Motion.altitude (altitude r0 source).toNat (altitude r1 target).toNat s := by
  obtain ⟨hz0, hz0b⟩ := altitude_bounds r0 source hr0 hsource
  obtain ⟨hz1, hz1b⟩ := altitude_bounds r1 target hr1 htarget
  split
  · apply Motion.rest_clearance _ _ hs0 hs1
    · exact_mod_cast hz0
    · exact_mod_cast hz1
  · rename_i ht
    exact accepted_forward_clearance r0 r1 _ _ _ _ hz0b hz1b
      (UInt64.le_iff_toNat_le.mpr hz0) (UInt64.le_iff_toNat_le.mpr hz1)
      (speed_le source) (speed_le target) hedge ht s hs0 hs1

#print axioms accepted_guards
#print axioms products_nat
#print axioms accepted_forward_clearance
#print axioms state_edge_clearance
end Project.Drone.Edges
