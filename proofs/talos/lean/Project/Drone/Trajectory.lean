import Project.Drone.Safety
import Project.Drone.Gluing

namespace Project.Drone.Trajectory
open LeanExe.Examples.Drone Arithmetic Feasibility Output Dynamics Safety
noncomputable section

def x (out : List UInt64) (i : Nat) (t : ℝ) : ℝ :=
  if out[2*i+1]! + out[2*(i+1)+1]! = 0 then
    Kinematics.restPosition (100*i) (duration out i) t
  else Kinematics.forwardPosition (100*i) (real out[2*i+1]!)
    (real out[2*(i+1)+1]!) t

def vx (out : List UInt64) (i : Nat) (t : ℝ) : ℝ :=
  if out[2*i+1]! + out[2*(i+1)+1]! = 0 then
    Kinematics.restVelocity (duration out i) t
  else Kinematics.forwardVelocity (real out[2*i+1]!) (real out[2*(i+1)+1]!) t

def z (out : List UInt64) (i : Nat) (t : ℝ) : ℝ :=
  Kinematics.verticalPosition (real out[2*i]!) (real out[2*(i+1)]!) (duration out i) t

def vz (out : List UInt64) (i : Nat) (t : ℝ) : ℝ :=
  Kinematics.verticalVelocity (real out[2*(i+1)]! - real out[2*i]!) (duration out i) t

theorem compute_speed_bound (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i < terrain.size) :
    (compute terrain).toList[2*i+1]!.toNat ≤ 20 := by
  obtain ⟨q, _, _, hv⟩ := Safety.waypoint (compute_correct terrain h (by omega)).2.1 i (by omega)
  rw [hv]
  exact speed_le q

theorem compute_duration_pos (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) : 0 < duration (compute terrain).toList i :=
  (compute_segment_maneuverable terrain h i hi 0 (by norm_num) (by norm_num)).1

theorem stopped_words (u v : UInt64) (hu : u.toNat ≤ 20) (hv : v.toNat ≤ 20)
    (ht : u+v = 0) : u = 0 ∧ v = 0 := by
  have hs := (Edges.products_nat 0 u v (by decide) hu hv).1
  rw [ht] at hs
  change 0 = u.toNat+v.toNat at hs
  exact ⟨UInt64.toNat_inj.mp (by change u.toNat = 0; omega),
    UInt64.toNat_inj.mp (by change v.toNat = 0; omega)⟩

/-- Both horizontal primitives meet their supplied waypoint positions and speeds. -/
theorem horizontal_endpoints (out : List UInt64) (i : Nat)
    (hu : out[2*i+1]!.toNat ≤ 20) (hv : out[2*(i+1)+1]!.toNat ≤ 20)
    (hT : 0 < duration out i) :
    x out i 0 = 100*i ∧ x out i (duration out i) = 100*(i+1) ∧
    vx out i 0 = real out[2*i+1]! ∧
    vx out i (duration out i) = real out[2*(i+1)+1]! := by
  by_cases ht : out[2*i+1]! + out[2*(i+1)+1]! = 0
  · obtain ⟨hu0, hv0⟩ := stopped_words _ _ hu hv ht
    simp [x, vx, ht, Kinematics.restPosition, Kinematics.restVelocity,
      Motion.smooth, ne_of_gt hT, hu0, hv0, real]
    ring
  · have hp := total_positive _ _ hu hv ht
    have he := Kinematics.forward_endpoints (100*i) (real out[2*i+1]!)
      (real out[2*(i+1)+1]!) (ne_of_gt hp)
    simp only [x, vx, duration, ht, ite_false]
    simpa only [mul_add, mul_one] using he

theorem vertical_endpoints (out : List UInt64) (i : Nat) (hT : 0 < duration out i) :
    z out i 0 = real out[2*i]! ∧ z out i (duration out i) = real out[2*(i+1)]! ∧
    vz out i 0 = 0 ∧ vz out i (duration out i) = 0 :=
  Kinematics.vertical_endpoints _ _ _ (ne_of_gt hT)

theorem horizontal_derivative (out : List UInt64) (i : Nat)
    (hu : out[2*i+1]!.toNat ≤ 20) (hv : out[2*(i+1)+1]!.toNat ≤ 20) (t : ℝ) :
    HasDerivAt (x out i) (vx out i t) t := by
  unfold x vx
  by_cases ht : out[2*i+1]! + out[2*(i+1)+1]! = 0
  · simpa only [x, vx, ht, ite_true] using Kinematics.rest_derivative (100*i) (duration out i) t
  · simpa only [x, vx, ht, ite_false] using Kinematics.forward_derivative (100*i)
      (real out[2*i+1]!) (real out[2*(i+1)+1]!) t
      (ne_of_gt (total_positive _ _ hu hv ht))

theorem vertical_derivative (out : List UInt64) (i : Nat) (t : ℝ) :
    HasDerivAt (z out i) (vz out i t) t := Kinematics.vertical_derivative _ _ _ t

theorem vx_continuous (out : List UInt64) (i : Nat) : Continuous (vx out i) := by
  unfold vx
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : out[2*i+1]! + out[2*(i+1)+1]! = 0
  · simpa only [vx, ht, ite_true] using (Kinematics.rest_second_derivative (duration out i) t).continuousAt
  · simpa only [vx, ht, ite_false] using (Kinematics.forward_second_derivative
      (real out[2*i+1]!) (real out[2*(i+1)+1]!) t).continuousAt

theorem vz_continuous (out : List UInt64) (i : Nat) : Continuous (vz out i) :=
  continuous_iff_continuousAt.mpr fun t => (Kinematics.vertical_second_derivative _ _ t).continuousAt

/-- Every adjacent pair of returned primitives joins with matching position
and velocity. This includes moving/rest transitions; acceleration may jump. -/
theorem compute_joins (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+2 < terrain.size) :
    let out := (compute terrain).toList
    x out i (duration out i) = x out (i+1) 0 ∧
    z out i (duration out i) = z out (i+1) 0 ∧
    vx out i (duration out i) = vx out (i+1) 0 ∧
    vz out i (duration out i) = vz out (i+1) 0 := by
  have hl := horizontal_endpoints (compute terrain).toList i
    (compute_speed_bound terrain h i (by omega))
    (compute_speed_bound terrain h (i+1) (by omega))
    (compute_duration_pos terrain h i (by omega))
  have hr := horizontal_endpoints (compute terrain).toList (i+1)
    (compute_speed_bound terrain h (i+1) (by omega))
    (compute_speed_bound terrain h (i+2) hi)
    (compute_duration_pos terrain h (i+1) (by omega))
  have zl := vertical_endpoints (compute terrain).toList i (compute_duration_pos terrain h i (by omega))
  have zr := vertical_endpoints (compute terrain).toList (i+1) (compute_duration_pos terrain h (i+1) (by omega))
  exact ⟨hl.2.1.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hr.1.symm), zl.2.1.trans zr.1.symm,
    hl.2.2.2.trans hr.2.2.1.symm, zl.2.2.2.trans zr.2.2.1.symm⟩

/-- The source output defines a single trajectory on cumulative physical time. -/
def globalX (terrain : Array UInt64) : ℝ → ℝ :=
  Gluing.stitch 0 (x (compute terrain).toList) (duration (compute terrain).toList) (terrain.size-1)

def globalZ (terrain : Array UInt64) : ℝ → ℝ :=
  Gluing.stitch (real (compute terrain)[0]!) (z (compute terrain).toList)
    (duration (compute terrain).toList) (terrain.size-1)

def globalVx (terrain : Array UInt64) : ℝ → ℝ :=
  Gluing.stitch 0 (vx (compute terrain).toList) (duration (compute terrain).toList) (terrain.size-1)

def globalVz (terrain : Array UInt64) : ℝ → ℝ :=
  Gluing.stitch 0 (vz (compute terrain).toList) (duration (compute terrain).toList) (terrain.size-1)

/-- The reconstructed global trajectory has the stated derivative everywhere,
including takeoff and all internal joins, and both velocity components are
continuous. The flight is its restriction to [0, clock duration (size-1)]. -/
theorem compute_global_smooth (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) :
    (∀ t, HasDerivAt (globalX terrain) (globalVx terrain t) t) ∧
    (∀ t, HasDerivAt (globalZ terrain) (globalVz terrain t) t) ∧
    Continuous (globalVx terrain) ∧ Continuous (globalVz terrain) := by
  have hs0 : (compute terrain).toList[1]! = 0 := by
    have hp := congrArg (fun xs : List UInt64 => xs[1]!) (compute_endpoints terrain h hn).1
    simpa [List.getElem!_eq_getElem?_getD] using hp
  have hx := Gluing.stitch_smooth 0 0 (x (compute terrain).toList) (vx (compute terrain).toList)
    (duration (compute terrain).toList) (terrain.size-1)
    (fun i hi => compute_duration_pos terrain h i (by omega))
    (fun i hi t => horizontal_derivative _ i (compute_speed_bound terrain h i (by omega))
      (compute_speed_bound terrain h (i+1) (by omega)) t)
    (fun i _ => vx_continuous _ i) ?_ ?_ rfl
  · have hz := Gluing.stitch_smooth (real (compute terrain)[0]!) 0
      (z (compute terrain).toList) (vz (compute terrain).toList)
      (duration (compute terrain).toList) (terrain.size-1)
      (fun i hi => compute_duration_pos terrain h i (by omega))
      (fun i _ t => vertical_derivative _ i t) (fun i _ => vz_continuous _ i) ?_ ?_ rfl
    · exact ⟨hx.1, hz.1, hx.2, hz.2⟩
    · intro hN
      have e := vertical_endpoints (compute terrain).toList 0
        (compute_duration_pos terrain h 0 (by omega))
      exact ⟨by simpa only [Nat.mul_zero, Array.getElem!_toList] using e.1.symm, e.2.2.1.symm⟩
    · intro i hi
      have e := compute_joins terrain h i (by omega)
      exact ⟨e.2.1, e.2.2.2⟩
  · intro hN
    have e := horizontal_endpoints (compute terrain).toList 0
      (compute_speed_bound terrain h 0 hn) (compute_speed_bound terrain h 1 (by omega))
      (compute_duration_pos terrain h 0 (by omega))
    exact ⟨by simpa using e.1.symm, by simpa [hs0, real] using e.2.2.1.symm⟩
  · intro i hi
    have e := compute_joins terrain h i (by omega)
    exact ⟨e.1, e.2.2.1⟩

#print axioms compute_joins
#print axioms compute_global_smooth
end
end Project.Drone.Trajectory
