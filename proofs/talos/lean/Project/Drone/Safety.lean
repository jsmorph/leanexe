import Project.Drone.Output
import Project.Drone.Kinematics

namespace Project.Drone.Safety
open LeanExe.Examples.Drone Arithmetic Feasibility Output Dynamics

def PairAt (terrain : Array UInt64) (output : List UInt64) (i state : Nat) : Prop :=
  output[2*i]! = altitude (floorAt terrain i) state ∧
  output[2*i+1]! = speed state

private theorem word_append_left (xs ys : List UInt64) (i : Nat) (hi : i < xs.length) :
    (xs ++ ys)[i]! = xs[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem word_append_right (xs ys : List UInt64) (i : Nat) (hi : xs.length ≤ i) :
    (xs ++ ys)[i]! = ys[i-xs.length]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append_right hi]

theorem state_bound {terrain n state c output} (h : Encoded terrain n state c output) :
    state < stateCount := by
  cases h with
  | start => decide
  | step _ hs _ _ => exact hs

theorem last_words {terrain n state c output} (h : Encoded terrain n state c output) :
    PairAt terrain output n state := by
  cases h with
  | start => simp [PairAt, altitude, speed]
  | @step n source target c output previous _ _ _ =>
    have hp := previous.length
    unfold PairAt
    rw [word_append_right _ _ _ (by omega : output.length ≤ 2*(n+1)),
      word_append_right _ _ _ (by omega : output.length ≤ 2*(n+1)+1)]
    simp [hp]

private theorem pair_append {terrain n state c output i q}
    (h : Encoded terrain n state c output) (hi : i ≤ n)
    (pair : PairAt terrain output i q) (suffix : List UInt64) :
    PairAt terrain (output ++ suffix) i q := by
  have hp := h.length
  simpa only [PairAt, word_append_left _ _ _ (by omega : 2*i < output.length),
    word_append_left _ _ _ (by omega : 2*i+1 < output.length)] using pair

/-- Each actual output pair decodes to one of the planner's bounded states. -/
theorem waypoint {terrain n state c output} (h : Encoded terrain n state c output)
    (i : Nat) (hi : i ≤ n) : ∃ q, q < stateCount ∧ PairAt terrain output i q := by
  induction h with
  | start =>
    have : i = 0 := by omega
    subst i
    exact ⟨0, by decide, last_words Encoded.start⟩
  | @step n source target c output previous ht hall hedge ih =>
    by_cases heq : i = n+1
    · subst i
      exact ⟨target, ht, last_words (Encoded.step previous ht hall hedge)⟩
    · obtain ⟨q, hq, hp⟩ := ih (by omega)
      exact ⟨q, hq, pair_append previous (by omega) hp _⟩

/-- Every adjacent pair in the actual word list is joined by an admitted edge. -/
theorem adjacent {terrain n state c output} (h : Encoded terrain n state c output)
    (i : Nat) (hi : i < n) :
    ∃ a b, a < stateCount ∧ b < stateCount ∧ PairAt terrain output i a ∧
      PairAt terrain output (i+1) b ∧
      0 < edgeTicks (floorAt terrain i) (floorAt terrain (i+1))
        (altitude (floorAt terrain i) a) (altitude (floorAt terrain (i+1)) b)
        (speed a) (speed b) := by
  induction h with
  | start => omega
  | @step n source target c output previous ht hall hedge ih =>
    by_cases heq : i = n
    · subst i
      exact ⟨source, target, state_bound previous, ht,
        pair_append previous (by omega) (last_words previous) _,
        last_words (Encoded.step previous ht hall hedge), hedge⟩
    · obtain ⟨a, b, ha, hb, hpa, hpb, he⟩ := ih (by omega)
      exact ⟨a, b, ha, hb, pair_append previous (by omega) hpa _,
        pair_append previous (by omega) hpb _, he⟩

/-- A direct array-index statement of the interior waypoint clearance. -/
theorem compute_interior (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi0 : 0 < i) (hi1 : i+1 < terrain.size) :
    terrain[i]!.toNat+100 ≤ (compute terrain)[2*i]!.toNat ∧
    (compute terrain)[2*i+1]!.toNat ≤ 20 := by
  have he := (compute_correct terrain h (by omega)).2.1
  obtain ⟨q, hq, hz, hv⟩ := waypoint he i (by omega)
  simp only [Array.getElem!_toList] at hz hv
  rw [hz, hv]
  have ha := (altitude_bounds (floorAt terrain i) q (floorAt_bound terrain h i (by omega)) hq).1
  rw [interior_clearance terrain h i hi0 hi1] at ha
  exact ⟨ha, speed_le q⟩

noncomputable section

/-- Continuous spatial-floor clearance for every segment of the returned array.
This includes the takeoff/landing ramps defined by `floorAt`. -/
theorem compute_segment_clearance (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let out := compute terrain
    Motion.floor (floorAt terrain i).toNat (floorAt terrain (i+1)).toNat
      (if out[2*i+1]! + out[2*(i+1)+1]! = 0 then Motion.smooth s
       else Motion.fraction out[2*i+1]!.toNat out[2*(i+1)+1]!.toNat s) ≤
      Motion.altitude out[2*i]!.toNat out[2*(i+1)]!.toNat s := by
  dsimp only
  obtain ⟨a, b, ha, hb, ⟨hza, hva⟩, ⟨hzb, hvb⟩, he⟩ :=
    adjacent (compute_correct terrain h (by omega)).2.1 i (by omega)
  simp only [Array.getElem!_toList] at hza hva hzb hvb
  rw [hza, hva, hzb, hvb]
  exact Edges.state_edge_clearance _ _ a b
    (floorAt_bound terrain h i (by omega)) (floorAt_bound terrain h (i+1) hi)
    ha hb he s hs0 hs1

/-- Segment duration reconstructed from the returned waypoint words. -/
def duration (output : List UInt64) (i : Nat) : ℝ :=
  if output[2*i+1]! + output[2*(i+1)+1]! = 0 then
    real (restSeconds (distance output[2*i]! output[2*(i+1)]!))
  else 200/(real output[2*i+1]! + real output[2*(i+1)+1]!)

/-- All component bounds, using the appropriate horizontal primitive. -/
def Maneuverable (z0 z1 u v : UInt64) (T s : ℝ) : Prop :=
  0 < T ∧
  (if u+v = 0 then
    (0 ≤ 100*(6*s*(1-s))/T ∧ 100*(6*s*(1-s))/T ≤ 20) ∧
    |100*(6-12*s)/T^2| ≤ 1
   else
    (0 ≤ (1-s)*real u+s*real v ∧ (1-s)*real u+s*real v ≤ 20) ∧
    |(real v^2-real u^2)/200| ≤ 1) ∧
  |(real z1-real z0)*(6*s*(1-s))/T| ≤ 20 ∧
  |(real z1-real z0)*(6-12*s)/T^2| ≤ 4

/-- The returned trajectory obeys all four component limits at every
normalized segment time, using its actual integer-computed duration. -/
theorem compute_segment_maneuverable (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    let out := (compute terrain).toList
    Maneuverable out[2*i]! out[2*(i+1)]! out[2*i+1]! out[2*(i+1)+1]!
      (duration out i) s := by
  dsimp only
  obtain ⟨a, b, ha, hb, ⟨hza, hva⟩, ⟨hzb, hvb⟩, he⟩ :=
    adjacent (compute_correct terrain h (by omega)).2.1 i (by omega)
  unfold duration Maneuverable
  rw [hza, hva, hzb, hvb]
  have hzaB := (altitude_bounds _ a (floorAt_bound terrain h i (by omega)) ha).2
  have hzbB := (altitude_bounds _ b (floorAt_bound terrain h (i+1) hi) hb).2
  by_cases ht : speed a + speed b = 0
  · simp only [ht, ite_true]
    obtain ⟨hT, hvx, hax, hvz, haz⟩ := rest_bounds _ _ hzaB hzbB s hs0 hs1
    exact ⟨hT, ⟨hvx, hax⟩, hvz, haz⟩
  · simp only [ht, ite_false]
    obtain ⟨hvx, hax, hvz, haz⟩ := accepted_forward_bounds _ _ _ _ _ _
      hzaB hzbB (speed_le a) (speed_le b) he ht s hs0 hs1
    have hT := (forward_conditions _ _ _ _ _ _ hzaB hzbB
      (speed_le a) (speed_le b) he ht).1
    exact ⟨hT, ⟨hvx, hax⟩, hvz, haz⟩

/-- Edge tick costs are exactly the real durations of the returned segments. -/
theorem compute_segment_timing (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i+1 < terrain.size) :
    let out := (compute terrain).toList
    real (edgeTicks (floorAt terrain i) (floorAt terrain (i+1))
      out[2*i]! out[2*(i+1)]! out[2*i+1]! out[2*(i+1)+1]!)/840 = duration out i := by
  dsimp only
  obtain ⟨a, b, ha, hb, ⟨hza, hva⟩, ⟨hzb, hvb⟩, he⟩ :=
    adjacent (compute_correct terrain h (by omega)).2.1 i (by omega)
  unfold duration
  rw [hza, hva, hzb, hvb]
  split
  · rename_i ht
    have hsum := (Edges.products_nat 0 (speed a) (speed b) (by decide)
      (speed_le a) (speed_le b)).1
    rw [ht] at hsum
    have h0 : (speed a).toNat = 0 ∧ (speed b).toNat = 0 := by
      change 0 = (speed a).toNat + (speed b).toNat at hsum
      omega
    have hua : speed a = 0 := UInt64.toNat_inj.mp h0.1
    have hvb : speed b = 0 := UInt64.toNat_inj.mp h0.2
    rw [hua, hvb]
    have hzaB := (altitude_bounds _ a (floorAt_bound terrain h i (by omega)) ha).2
    have hzbB := (altitude_bounds _ b (floorAt_bound terrain h (i+1) hi) hb).2
    dsimp [real]
    rw [Timing.rest_ticks _ _ _ _ hzaB hzbB]
    push_cast
    ring
  · rename_i ht
    exact Timing.state_ticks_exact _ _ _ _ a b he ht

#print axioms compute_interior
#print axioms compute_segment_clearance
#print axioms compute_segment_maneuverable
#print axioms compute_segment_timing
end
end Project.Drone.Safety
