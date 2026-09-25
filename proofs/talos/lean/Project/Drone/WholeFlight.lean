import Project.Drone.Acceleration
import Project.Drone.Corridor

namespace Project.Drone.WholeFlight
open LeanExe.Examples.Drone Arithmetic Feasibility Output Dynamics Safety Trajectory
open Set
noncomputable section

/-- Arrival time in physical seconds, obtained from the actual returned words. -/
def flightTime (terrain : Array UInt64) : ℝ :=
  Gluing.clock (duration (compute terrain).toList) (terrain.size-1)

theorem compute_flightTime_nonneg (terrain : Array UInt64) (h : terrainBound terrain) :
    0 ≤ flightTime terrain :=
  Gluing.clock_mono _ (terrain.size-1)
    (fun i hi => le_of_lt (compute_duration_pos terrain h i (by omega))) 0 (by omega)

theorem compute_flightTime_pos (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 1 < terrain.size) : 0 < flightTime terrain := by
  have hm := Gluing.clock_mono (duration (compute terrain).toList) (terrain.size-1)
    (fun i hi => le_of_lt (compute_duration_pos terrain h i (by omega))) 1 (by omega)
  have hd := compute_duration_pos terrain h 0 hn
  simp only [Gluing.clock, zero_add] at hm
  exact lt_of_lt_of_le hd hm

private theorem first_word (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) : (compute terrain)[0]! = terrain[0]! := by
  have he := congrArg (fun xs : List UInt64 => xs[0]!) (compute_endpoints terrain h hn).1
  have hw : (compute terrain).toList[0]! = terrain[0]! := by
    simpa [List.getElem!_eq_getElem?_getD] using he
  simpa only [Array.getElem!_toList] using hw

/-- A singleton input has zero flight time and a constant, stopped ground path. -/
theorem compute_singleton (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : terrain.size = 1) :
    flightTime terrain = 0 ∧ ∀ t,
      globalX terrain t = 0 ∧ globalZ terrain t = real terrain[0]! ∧
      globalVx terrain t = 0 ∧ globalVz terrain t = 0 := by
  have hw := first_word terrain h (by omega)
  simp [flightTime, globalX, globalZ, globalVx, globalVz, hn,
    Gluing.clock, Gluing.stitch, hw]

/-- Departure and arrival of the assembled path, not just its encoded words. -/
theorem compute_global_endpoints (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) :
    (globalX terrain 0 = 0 ∧ globalZ terrain 0 = real terrain[0]! ∧
      globalVx terrain 0 = 0 ∧ globalVz terrain 0 = 0) ∧
    (globalX terrain (flightTime terrain) = 100*(terrain.size-1 : Nat) ∧
      globalZ terrain (flightTime terrain) = real terrain[terrain.size-1]! ∧
      globalVx terrain (flightTime terrain) = 0 ∧ globalVz terrain (flightTime terrain) = 0) := by
  by_cases hs : terrain.size = 1
  · have hc := compute_singleton terrain h hs
    simpa [hc.1, hs] using And.intro (hc.2 0) (hc.2 0)
  have hn2 : 1 < terrain.size := by omega
  constructor
  · have hg := compute_global_segment terrain h 0 hn2 0 (by norm_num)
      (le_of_lt (compute_duration_pos terrain h 0 hn2))
    have hf := compute_first terrain h hn2
    simp only [Gluing.clock, zero_add] at hg
    exact ⟨hg.1.trans hf.1, hg.2.1.trans (hf.2.1.trans (congrArg real (first_word terrain h hn))),
      hg.2.2.1.trans hf.2.2.1, hg.2.2.2.trans hf.2.2.2⟩
  · let i := terrain.size-2
    have hi : i+1 < terrain.size := by dsimp [i]; omega
    have hin : i+1 = terrain.size-1 := by dsimp [i]; omega
    have hT := compute_duration_pos terrain h i hi
    have hg := compute_global_segment terrain h i hi (duration (compute terrain).toList i)
      (le_of_lt hT) le_rfl
    have hx := horizontal_endpoints (compute terrain).toList i
      (compute_speed_bound terrain h i (by omega)) (compute_speed_bound terrain h (i+1) hi) hT
    have hz := vertical_endpoints (compute terrain).toList i hT
    have hw := Safety.last_words (compute_correct terrain h hn).2.1
    have hw' : (compute terrain).toList[2*(i+1)]! = terrain[terrain.size-1]! ∧
        (compute terrain).toList[2*(i+1)+1]! = 0 := by
      simpa [Safety.PairAt, altitude, speed, floorAt_last terrain hn, hin] using hw
    have hc : Gluing.clock (duration (compute terrain).toList) i+
        duration (compute terrain).toList i = flightTime terrain := by
      change Gluing.clock (duration (compute terrain).toList) (i+1) = flightTime terrain
      rw [hin]
      rfl
    dsimp only at hg
    rw [hc] at hg
    refine ⟨hg.1.trans ?_, hg.2.1.trans (hz.2.1.trans (congrArg real hw'.1)),
      hg.2.2.1.trans (hx.2.2.2.trans ?_), hg.2.2.2.trans hz.2.2.2⟩
    · have hir : (i : ℝ)+1 = (terrain.size-1 : Nat) := by exact_mod_cast hin
      simpa only [hir] using hx.2.1
    · simp [hw'.2, real]

/-- Coverage expressed in normalized time, for transferring all local bounds
to an arbitrary physical time in the finite flight. -/
theorem compute_normalized_cover (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 1 < terrain.size) (t : ℝ) (ht : t ∈ Icc 0 (flightTime terrain)) :
    ∃ i, i+1 < terrain.size ∧ ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      t = Gluing.clock (duration (compute terrain).toList) i+s*duration (compute terrain).toList i := by
  obtain ⟨i, hi, ha, hb⟩ := compute_global_cover terrain h hn t ht.1 ht.2
  have hT := compute_duration_pos terrain h i hi
  refine ⟨i, hi, (t-Gluing.clock (duration (compute terrain).toList) i)/duration (compute terrain).toList i,
    div_nonneg (sub_nonneg.mpr ha) (le_of_lt hT),
    (div_le_one hT).mpr (by linarith), ?_⟩
  rw [div_mul_cancel₀ _ (ne_of_gt hT)]
  ring

/-- Every physical time in the finite flight satisfies spatial clearance,
stays inside the terrain extent, and obeys both component speed limits. -/
theorem compute_throughout (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) (t : ℝ) (ht : t ∈ Icc 0 (flightTime terrain)) :
    (0 ≤ globalX terrain t ∧ globalX terrain t ≤ 100*(terrain.size-1 : Nat)) ∧
    Corridor.height terrain (globalX terrain t) ≤ globalZ terrain t ∧
    (0 ≤ globalVx terrain t ∧ globalVx terrain t ≤ 20) ∧ |globalVz terrain t| ≤ 20 := by
  by_cases hs : terrain.size = 1
  · have hc := (compute_singleton terrain h hs).2 t
    rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
    simp [hs, Corridor.height, Gluing.stitch, floorAt_first]
  obtain ⟨i, hi, s, hs0, hs1, he⟩ := compute_normalized_cover terrain h (by omega) t ht
  rw [he]
  have hp := Corridor.compute_spatial_segment terrain h i hi s hs0 hs1
  have hv := compute_global_speed terrain h i hi s hs0 hs1
  have hiR : (i : ℝ)+1 ≤ (terrain.size-1 : Nat) := by exact_mod_cast (show i+1 ≤ terrain.size-1 by omega)
  refine ⟨⟨?_, ?_⟩, hp.2, hv⟩
  · exact le_trans (by positivity) hp.1.1
  · nlinarith [hp.1.2]

/-- Every flight time away from a waypoint has bounded ordinary acceleration.
The exclusion is only the finite set of cumulative waypoint times. -/
theorem compute_acceleration_away_from_joins (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) (t : ℝ) (ht : t ∈ Icc 0 (flightTime terrain))
    (hj : ∀ i, i < terrain.size → t ≠ Gluing.clock (duration (compute terrain).toList) i) :
    ∃ aₓ a_z : ℝ, HasDerivAt (globalVx terrain) aₓ t ∧
      HasDerivAt (globalVz terrain) a_z t ∧ |aₓ| ≤ 1 ∧ |a_z| ≤ 4 := by
  have hn2 : 1 < terrain.size := by
    by_contra hn2
    have hs : terrain.size = 1 := by omega
    have hc := (compute_singleton terrain h hs).1
    have ht0 : t = 0 := by have := ht.1; have := ht.2; rw [hc] at this; linarith
    exact hj 0 hn (by simpa [Gluing.clock] using ht0)
  obtain ⟨i, hi, ha, hb⟩ := compute_global_cover terrain h hn2 t ht.1 ht.2
  have hleft := hj i (by omega)
  have hright := hj (i+1) hi
  simp only [Gluing.clock] at hright
  have hx := compute_global_acceleration terrain h i hi
    (t-Gluing.clock (duration (compute terrain).toList) i)
    (by rcases lt_or_eq_of_le ha with hlt | heq; linarith; exact (hleft heq.symm).elim)
    (by rcases lt_or_eq_of_le hb with hlt | heq; linarith; exact (hright heq).elim)
  exact ⟨_, _, by simpa only [add_sub_cancel] using hx⟩

/-- Safety of the source planner's actual global trajectory on its finite
flight interval. The acceleration fields distinguish ordinary derivatives
between joins from derivatives within each closed segment at its endpoints. -/
structure Safe (terrain : Array UInt64) : Prop where
  output_size : (compute terrain).size = 2*terrain.size
  time_nonnegative : 0 ≤ flightTime terrain
  time_positive : 1 < terrain.size → 0 < flightTime terrain
  position_derivatives :
    (∀ t, HasDerivAt (globalX terrain) (globalVx terrain t) t) ∧
    (∀ t, HasDerivAt (globalZ terrain) (globalVz terrain t) t)
  position_continuous : Continuous (globalX terrain) ∧ Continuous (globalZ terrain)
  velocity_continuous : Continuous (globalVx terrain) ∧ Continuous (globalVz terrain)
  departure : globalX terrain 0 = 0 ∧ globalZ terrain 0 = real terrain[0]! ∧
    globalVx terrain 0 = 0 ∧ globalVz terrain 0 = 0
  arrival : globalX terrain (flightTime terrain) = 100*(terrain.size-1 : Nat) ∧
    globalZ terrain (flightTime terrain) = real terrain[terrain.size-1]! ∧
    globalVx terrain (flightTime terrain) = 0 ∧ globalVz terrain (flightTime terrain) = 0
  throughout : ∀ t ∈ Icc 0 (flightTime terrain),
    (0 ≤ globalX terrain t ∧ globalX terrain t ≤ 100*(terrain.size-1 : Nat)) ∧
    Corridor.height terrain (globalX terrain t) ≤ globalZ terrain t ∧
    (0 ≤ globalVx terrain t ∧ globalVx terrain t ≤ 20) ∧ |globalVz terrain t| ≤ 20
  acceleration_away_from_joins : ∀ t ∈ Icc 0 (flightTime terrain),
    (∀ i, i < terrain.size → t ≠ Gluing.clock (duration (compute terrain).toList) i) →
    ∃ aₓ a_z : ℝ, HasDerivAt (globalVx terrain) aₓ t ∧
      HasDerivAt (globalVz terrain) a_z t ∧ |aₓ| ≤ 1 ∧ |a_z| ≤ 4
  acceleration : ∀ i, i+1 < terrain.size → ∀ t ∈ Ioo 0 (duration (compute terrain).toList i),
    let out := (compute terrain).toList
    let time := Gluing.clock (duration out) i+t
    HasDerivAt (globalVx terrain) (ax out i t) time ∧
    HasDerivAt (globalVz terrain) (az out i t) time ∧ |ax out i t| ≤ 1 ∧ |az out i t| ≤ 4
  acceleration_within : ∀ i, i+1 < terrain.size → ∀ t ∈ Icc 0 (duration (compute terrain).toList i),
    let out := (compute terrain).toList
    let a := Gluing.clock (duration out) i
    HasDerivWithinAt (globalVx terrain) (ax out i t) (Icc a (a+duration out i)) (a+t) ∧
    HasDerivWithinAt (globalVz terrain) (az out i t) (Icc a (a+duration out i)) (a+t) ∧
    |ax out i t| ≤ 1 ∧ |az out i t| ≤ 4
  singleton : terrain.size = 1 → flightTime terrain = 0 ∧ ∀ t,
    globalX terrain t = 0 ∧ globalZ terrain t = real terrain[0]! ∧
    globalVx terrain t = 0 ∧ globalVz terrain t = 0

/-- Every accepted nonempty terrain produces a safe whole flight under the
specified point-mass model. This is source correctness, not WASM execution
agreement; the corridor retains the specified takeoff and landing ramps. -/
theorem compute_safe (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) : Safe terrain := by
  have hs := compute_global_smooth terrain h hn
  have he := compute_global_endpoints terrain h hn
  exact {
    output_size := (compute_correct terrain h hn).1
    time_nonnegative := compute_flightTime_nonneg terrain h
    time_positive := compute_flightTime_pos terrain h
    position_derivatives := ⟨hs.1, hs.2.1⟩
    position_continuous := ⟨continuous_iff_continuousAt.mpr fun t => (hs.1 t).continuousAt,
      continuous_iff_continuousAt.mpr fun t => (hs.2.1 t).continuousAt⟩
    velocity_continuous := hs.2.2
    departure := he.1
    arrival := he.2
    throughout := compute_throughout terrain h hn
    acceleration_away_from_joins := compute_acceleration_away_from_joins terrain h hn
    acceleration := fun i hi t ht => compute_global_acceleration terrain h i hi t ht.1 ht.2
    acceleration_within := fun i hi t ht => compute_global_acceleration_within terrain h i hi t ht.1 ht.2
    singleton := compute_singleton terrain h
  }

end
end Project.Drone.WholeFlight
