import Project.Drone.Trajectory

namespace Project.Drone.Corridor
open LeanExe.Examples.Drone Arithmetic Feasibility Dynamics Safety Trajectory
noncomputable section

/-- The spatial clearance corridor linearly interpolates `floorAt` at the
100-unit terrain stations. Thus it has the specified takeoff/landing ramps,
100-unit clearance on interior segments, and the ground height for a singleton.
Only its restriction to the terrain's horizontal extent is used for safety. -/
def height (terrain : Array UInt64) : ℝ → ℝ :=
  Gluing.stitch (real (floorAt terrain 0))
    (fun i y => Motion.floor (real (floorAt terrain i))
      (real (floorAt terrain (i+1))) (y/100))
    (fun _ => 100) (terrain.size-1)

private theorem spatial_clock (i : Nat) : Gluing.clock (fun _ => (100 : ℝ)) i = 100*i := by
  induction i with
  | zero => simp [Gluing.clock]
  | succ i ih => simp [Gluing.clock, ih, Nat.cast_add, mul_add]

/-- Evaluation of the corridor at an actual horizontal position in a segment. -/
theorem height_on_segment (terrain : Array UInt64) (i : Nat) (hi : i+1 < terrain.size)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    height terrain (100*i+100*q) =
      Motion.floor (real (floorAt terrain i)) (real (floorAt terrain (i+1))) q := by
  have he := Gluing.stitch_on_segment (real (floorAt terrain 0))
    (fun j y => Motion.floor (real (floorAt terrain j))
      (real (floorAt terrain (j+1))) (y/100))
    (fun _ => 100) (terrain.size-1)
    (fun _ _ => by norm_num)
    (fun _ => by simp [Motion.floor])
    (fun j _ => by simp [Motion.floor])
    i (by omega) (100*q) (by positivity) (by linarith)
  simpa only [height, spatial_clock, mul_div_cancel_left₀ _ (by norm_num : (100 : ℝ) ≠ 0)] using he

/-- Horizontal fraction selected by the actual returned speed words. -/
def progress (out : List UInt64) (i : Nat) (s : ℝ) : ℝ :=
  if out[2*i+1]! + out[2*(i+1)+1]! = 0 then Motion.smooth s
  else Motion.fraction (real out[2*i+1]!) (real out[2*(i+1)+1]!) s

theorem compute_progress_bounds (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ progress (compute terrain).toList i s ∧ progress (compute terrain).toList i s ≤ 1 := by
  unfold progress
  split
  · exact Motion.smooth_bounds hs0 hs1
  · rename_i ht
    exact Kinematics.fraction_bounds _ _ s (by unfold real; positivity)
      (by unfold real; positivity)
      (Dynamics.total_positive _ _ (compute_speed_bound terrain h i (by omega))
        (compute_speed_bound terrain h (i+1) hi) ht) hs0 hs1

theorem x_normalized (out : List UInt64) (i : Nat) (hT : 0 < duration out i) (s : ℝ) :
    x out i (s*duration out i) = 100*i+100*progress out i s := by
  unfold x progress
  split
  · simp only [Kinematics.restPosition, mul_div_cancel_right₀ _ (ne_of_gt hT)]
  · rename_i ht
    have hd : duration out i = 200/(real out[2*i+1]!+real out[2*(i+1)+1]!) := by
      simp only [duration, ht, ite_false]
    simp only [Kinematics.forwardPosition, ← hd, mul_div_cancel_right₀ _ (ne_of_gt hT)]

/-- Clearance is measured at global horizontal position, rather than merely
at the normalized time parameter of a primitive. The path stays in its
horizontal terrain segment throughout that primitive. -/
theorem compute_spatial_segment (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let out := (compute terrain).toList
    let time := Gluing.clock (duration out) i+s*duration out i
    (100*i ≤ globalX terrain time ∧ globalX terrain time ≤ 100*(i+1)) ∧
      height terrain (globalX terrain time) ≤ globalZ terrain time := by
  have hT := compute_duration_pos terrain h i hi
  have he := compute_global_segment terrain h i hi (s*duration (compute terrain).toList i)
    (mul_nonneg hs0 (le_of_lt hT)) (by nlinarith)
  have hp := compute_progress_bounds terrain h i hi s hs0 hs1
  dsimp only at he ⊢
  rw [he.1, x_normalized _ i hT s]
  refine ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩, ?_⟩
  rw [height_on_segment terrain i hi _ hp.1 hp.2]
  exact compute_global_clearance terrain h i hi s hs0 hs1

end
end Project.Drone.Corridor
