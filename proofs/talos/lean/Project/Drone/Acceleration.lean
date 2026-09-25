import Project.Drone.Trajectory

namespace Project.Drone.Trajectory
open LeanExe.Examples.Drone Arithmetic Feasibility Dynamics Safety
open Set
noncomputable section

/-- Physical-time horizontal acceleration of the selected primitive. -/
def ax (out : List UInt64) (i : Nat) (t : ℝ) : ℝ :=
  if out[2*i+1]! + out[2*(i+1)+1]! = 0 then
    100*(6-12*(t/duration out i))/(duration out i)^2
  else ((real out[2*(i+1)+1]!)^2-(real out[2*i+1]!)^2)/200

def az (out : List UInt64) (i : Nat) (t : ℝ) : ℝ :=
  Kinematics.verticalAcceleration (real out[2*(i+1)]! - real out[2*i]!)
    (duration out i) t

theorem horizontal_acceleration (out : List UInt64) (i : Nat) (t : ℝ) :
    HasDerivAt (vx out i) (ax out i t) t := by
  unfold vx ax
  split
  · exact Kinematics.rest_second_derivative _ t
  · exact Kinematics.forward_second_derivative _ _ t

theorem vertical_acceleration (out : List UInt64) (i : Nat) (t : ℝ) :
    HasDerivAt (vz out i) (az out i t) t :=
  Kinematics.vertical_second_derivative _ _ t

theorem compute_acceleration_bounds (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ duration (compute terrain).toList i) :
    |ax (compute terrain).toList i t| ≤ 1 ∧ |az (compute terrain).toList i t| ≤ 4 := by
  have hT := compute_duration_pos terrain h i hi
  have hm := compute_segment_maneuverable terrain h i hi
    (t/duration (compute terrain).toList i)
    (div_nonneg ht0 (le_of_lt hT)) ((div_le_one hT).mpr ht1)
  dsimp only at hm
  unfold Maneuverable at hm
  refine ⟨?_, hm.2.2.2⟩
  unfold ax
  split <;> rename_i ht <;> simp only [ht, ite_true, ite_false] at hm
  · exact hm.2.1.2
  · exact hm.2.1.2

/-- Agreement with a shifted primitive on a closed interval transports its
derivative, including the appropriate one-sided derivative at either endpoint. -/
private theorem derivative_within_shift (f g : ℝ → ℝ) (a T t dg : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ T)
    (he : ∀ u ∈ Icc a (a+T), f u = g (u-a))
    (hd : HasDerivAt g dg t) :
    HasDerivWithinAt f dg (Icc a (a+T)) (a+t) := by
  have shifted : HasDerivAt (fun u => g (u-a)) dg (a+t) := by
    have hd' : HasDerivAt g dg (a+t-a) := by simpa using hd
    simpa only [Function.comp_def, id_eq, mul_one] using
      hd'.comp (a+t) ((hasDerivAt_id (a+t)).sub_const a)
  exact shifted.hasDerivWithinAt.congr he (he _ ⟨by linarith, by linarith⟩)

/-- The acceleration bounds concern derivatives of the actual global velocity.
At a join each adjacent closed interval supplies its own one-sided derivative;
the two accelerations need not agree. -/
theorem compute_global_acceleration_within (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ duration (compute terrain).toList i) :
    let out := (compute terrain).toList
    let a := Gluing.clock (duration out) i
    HasDerivWithinAt (globalVx terrain) (ax out i t) (Icc a (a+duration out i)) (a+t) ∧
    HasDerivWithinAt (globalVz terrain) (az out i t) (Icc a (a+duration out i)) (a+t) ∧
    |ax out i t| ≤ 1 ∧ |az out i t| ≤ 4 := by
  dsimp only
  refine ⟨?_, ?_, compute_acceleration_bounds terrain h i hi t ht0 ht1⟩
  · apply derivative_within_shift _ (vx (compute terrain).toList i) _ _ _ _ ht0 ht1
      _ (horizontal_acceleration _ i t)
    intro u hu
    have he := compute_global_segment terrain h i hi
      (u-Gluing.clock (duration (compute terrain).toList) i)
      (by linarith [hu.1]) (by linarith [hu.2])
    simpa only [add_sub_cancel] using he.2.2.1
  · apply derivative_within_shift _ (vz (compute terrain).toList i) _ _ _ _ ht0 ht1
      _ (vertical_acceleration _ i t)
    intro u hu
    have he := compute_global_segment terrain h i hi
      (u-Gluing.clock (duration (compute terrain).toList) i)
      (by linarith [hu.1]) (by linarith [hu.2])
    simpa only [add_sub_cancel] using he.2.2.2

/-- Between joins the ordinary two-sided accelerations exist and obey the
component limits. No two-sided acceleration is asserted at a waypoint. -/
theorem compute_global_acceleration (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (t : ℝ) (ht0 : 0 < t)
    (ht1 : t < duration (compute terrain).toList i) :
    let out := (compute terrain).toList
    let time := Gluing.clock (duration out) i+t
    HasDerivAt (globalVx terrain) (ax out i t) time ∧
    HasDerivAt (globalVz terrain) (az out i t) time ∧
    |ax out i t| ≤ 1 ∧ |az out i t| ≤ 4 := by
  have ha := compute_global_acceleration_within terrain h i hi t
    (le_of_lt ht0) (le_of_lt ht1)
  exact ⟨ha.1.hasDerivAt (Icc_mem_nhds (by linarith) (by linarith)),
    ha.2.1.hasDerivAt (Icc_mem_nhds (by linarith) (by linarith)), ha.2.2⟩

end
end Project.Drone.Trajectory
