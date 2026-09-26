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

theorem compute_first (terrain : Array UInt64) (h : terrainBound terrain) (hn : 1 < terrain.size) :
    let out := (compute terrain).toList
    x out 0 0 = 0 ∧ z out 0 0 = real (compute terrain)[0]! ∧
    vx out 0 0 = 0 ∧ vz out 0 0 = 0 := by
  have hs0 : (compute terrain).toList[1]! = 0 := by
    have hp := congrArg (fun xs : List UInt64 => xs[1]!) (compute_endpoints terrain h (by omega)).1
    simpa [List.getElem!_eq_getElem?_getD] using hp
  have hx := horizontal_endpoints (compute terrain).toList 0
    (compute_speed_bound terrain h 0 (by omega)) (compute_speed_bound terrain h 1 hn)
    (compute_duration_pos terrain h 0 (by omega))
  have hz := vertical_endpoints (compute terrain).toList 0 (compute_duration_pos terrain h 0 (by omega))
  exact ⟨by simpa using hx.1,
    by simpa only [Nat.mul_zero, Array.getElem!_toList] using hz.1,
    by simpa [hs0, real] using hx.2.2.1, hz.2.2.1⟩

/-- The four global coordinates agree with the local primitive throughout
each cumulative-time interval, including its endpoints. -/
theorem compute_global_segment (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ duration (compute terrain).toList i) :
    let out := (compute terrain).toList
    let time := Gluing.clock (duration out) i+t
    globalX terrain time = x out i t ∧ globalZ terrain time = z out i t ∧
    globalVx terrain time = vx out i t ∧ globalVz terrain time = vz out i t := by
  have hf := compute_first terrain h (by omega)
  have hd : ∀ j, j < terrain.size-1 → 0 < duration (compute terrain).toList j :=
    fun j hj => compute_duration_pos terrain h j (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Gluing.stitch_on_segment _ _ _ _ hd (fun _ => hf.1.symm)
      (fun j hj => (compute_joins terrain h j (by omega)).1) i (by omega) t ht0 ht1
  · exact Gluing.stitch_on_segment _ _ _ _ hd (fun _ => hf.2.1.symm)
      (fun j hj => (compute_joins terrain h j (by omega)).2.1) i (by omega) t ht0 ht1
  · exact Gluing.stitch_on_segment _ _ _ _ hd (fun _ => hf.2.2.1.symm)
      (fun j hj => (compute_joins terrain h j (by omega)).2.2.1) i (by omega) t ht0 ht1
  · exact Gluing.stitch_on_segment _ _ _ _ hd (fun _ => hf.2.2.2.symm)
      (fun j hj => (compute_joins terrain h j (by omega)).2.2.2) i (by omega) t ht0 ht1

/-- Every time in a nontrivial flight belongs to one of those proved intervals. -/
theorem compute_global_cover (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 1 < terrain.size) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ Gluing.clock (duration (compute terrain).toList) (terrain.size-1)) :
    ∃ i, i+1 < terrain.size ∧
      Gluing.clock (duration (compute terrain).toList) i ≤ t ∧
      t ≤ Gluing.clock (duration (compute terrain).toList) i + duration (compute terrain).toList i := by
  obtain ⟨i, hi, ha, hb⟩ := Gluing.clock_cover (duration (compute terrain).toList)
    (terrain.size-1) (by omega) (fun j hj => compute_duration_pos terrain h j (by omega)) t ht0 ht1
  exact ⟨i, by omega, ha, hb⟩

/-- Segment clearance transported to the single global altitude function. -/
theorem compute_global_clearance (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let out := (compute terrain).toList
    Motion.floor (floorAt terrain i).toNat (floorAt terrain (i+1)).toNat
      (if out[2*i+1]! + out[2*(i+1)+1]! = 0 then Motion.smooth s
       else Motion.fraction out[2*i+1]!.toNat out[2*(i+1)+1]!.toNat s) ≤
      globalZ terrain (Gluing.clock (duration out) i+s*duration out i) := by
  have hT := compute_duration_pos terrain h i hi
  have he := compute_global_segment terrain h i hi (s*duration (compute terrain).toList i)
    (mul_nonneg hs0 (le_of_lt hT)) (by nlinarith)
  dsimp only at he ⊢
  rw [he.2.1]
  simp only [z, Kinematics.verticalPosition, mul_div_cancel_right₀ _ (ne_of_gt hT)]
  simpa only [Array.getElem!_toList, real] using compute_segment_clearance terrain h i hi s hs0 hs1

/-- Actual global velocity components obey the speed limits on every flight interval. -/
theorem compute_global_speed (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let out := (compute terrain).toList
    let time := Gluing.clock (duration out) i+s*duration out i
    (0 ≤ globalVx terrain time ∧ globalVx terrain time ≤ 20) ∧
      |globalVz terrain time| ≤ 20 := by
  have hT := compute_duration_pos terrain h i hi
  have he := compute_global_segment terrain h i hi (s*duration (compute terrain).toList i)
    (mul_nonneg hs0 (le_of_lt hT)) (by nlinarith)
  have hm := compute_segment_maneuverable terrain h i hi s hs0 hs1
  dsimp only at he hm ⊢
  rw [he.2.2.1, he.2.2.2]
  unfold vx vz Kinematics.restVelocity Kinematics.forwardVelocity Kinematics.verticalVelocity
  by_cases ht : (compute terrain).toList[2*i+1]! + (compute terrain).toList[2*(i+1)+1]! = 0
  · simp only [ht, ite_true, mul_div_cancel_right₀ _ (ne_of_gt hT)]
    simp only [Maneuverable, ht, ite_true] at hm
    exact ⟨hm.2.1.1, hm.2.2.1⟩
  · have hd : duration (compute terrain).toList i =
        200/(real (compute terrain).toList[2*i+1]! + real (compute terrain).toList[2*(i+1)+1]!) := by
      simp only [duration, ht, ite_false]
    simp only [ht, ite_false, ← hd, mul_div_cancel_right₀ _ (ne_of_gt hT)]
    simp only [Maneuverable, ht, ite_false] at hm
    exact ⟨hm.2.1.1, hm.2.2.1⟩

#print axioms compute_joins
#print axioms compute_global_smooth
#print axioms compute_global_segment
#print axioms compute_global_cover
#print axioms compute_global_clearance
#print axioms compute_global_speed
end
end Project.Drone.Trajectory
