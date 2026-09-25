import Project.Drone.Planner

namespace Project.Drone.Feasibility
open LeanExe.Examples.Drone Arithmetic Timing Planner Optimality

/-- Any bounded floor sequence has an all-stop flight. Endpoint-stop flags
may be imposed at any layer without invalidating this witness. -/
theorem all_stop_flight (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat)
    (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100) :
    ∃ c, Flight r stop n 0 c := by
  induction n with
  | zero => exact ⟨Cost.zero, Flight.start⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih (fun i hi => hr i (by omega))
    have hn : (r n).toNat ≤ heightLimit := by have := hr n (by omega); dsimp [heightLimit]; omega
    have hn1 : (r (n+1)).toNat ≤ heightLimit := by have := hr (n+1) (by omega); dsimp [heightLimit]; omega
    have hedge := (rest_admitted (r n) (r (n+1)) (r n) (r (n+1)) hn hn1).1
    refine ⟨c.add (edgeCost r n 0 0), Flight.step hc (by decide) (by simp) ?_⟩
    simpa [altitude, speed] using hedge

/-- The terminal stopped state is reachable in the actual DP row recurrence. -/
theorem terminal_finite (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat)
    (hn : n ≤ 64) (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100) :
    (layers r stop n)[0]! < infinity := by
  obtain ⟨c, hc⟩ := all_stop_flight r stop n hr
  exact ((layers_correct r stop n hn hr).2.2 0 c hc).1

/-- For every bounded input floor sequence, the final DP row has an attained
minimum-cost flight ending on the floor at rest. This does not yet prove the
public reconstruction loop returns that flight. -/
theorem terminal_optimal (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat)
    (hn : n ≤ 64) (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100) :
    Flight r stop n 0 (rowCost (layers r stop n) 0) ∧
    ∀ other, Flight r stop n 0 other →
      (rowCost (layers r stop n) 0).LE other :=
  layers_optimal r stop n 0 hn hr (by decide) (terminal_finite r stop n hn hr)

def terrainBound (terrain : Array UInt64) : Prop :=
  terrain.size ≤ 64 ∧ ∀ i, i < terrain.size → terrain[i]!.toNat ≤ 1000000

theorem floorAt_nat (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i < terrain.size) :
    (floorAt terrain i).toNat = terrain[i]!.toNat +
      (if i == 0 || i+1 == terrain.size then 0 else 100) := by
  have ht := h.2 i hi
  unfold floorAt
  split <;> rw [UInt64.toNat_add]
  · change (terrain[i]!.toNat+0)%18446744073709551616 = terrain[i]!.toNat+0
    exact Nat.mod_eq_of_lt (by omega)
  · change (terrain[i]!.toNat+100)%18446744073709551616 = terrain[i]!.toNat+100
    exact Nat.mod_eq_of_lt (by omega)

theorem floorAt_bound (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi : i < terrain.size) : (floorAt terrain i).toNat ≤ 1000100 := by
  rw [floorAt_nat terrain h i hi]
  have := h.2 i hi
  split <;> omega

theorem floorAt_first (terrain : Array UInt64) : floorAt terrain 0 = terrain[0]! := by
  simp [floorAt]

theorem floorAt_last (terrain : Array UInt64) (hn : 0 < terrain.size) :
    floorAt terrain (terrain.size-1) = terrain[terrain.size-1]! := by
  have heq : terrain.size-1+1 = terrain.size := by omega
  simp [floorAt, heq]

theorem interior_clearance (terrain : Array UInt64) (h : terrainBound terrain)
    (i : Nat) (hi0 : 0 < i) (hi1 : i+1 < terrain.size) :
    (floorAt terrain i).toNat = terrain[i]!.toNat+100 := by
  rw [floorAt_nat terrain h i (by omega)]
  simp [show i ≠ 0 by omega, show i+1 ≠ terrain.size by omega]

/-- Feasibility and optimality specialize to the actual terrain-floor function.
The public loop and reconstruction correspondence remain separate obligations. -/
theorem terrain_terminal_optimal (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) :
    let r := floorAt terrain
    let stop := fun i => i+1 == terrain.size
    let n := terrain.size-1
    Flight r stop n 0 (rowCost (layers r stop n) 0) ∧
    ∀ other, Flight r stop n 0 other → (rowCost (layers r stop n) 0).LE other := by
  apply terminal_optimal
  · have := h.1; omega
  · intro i hi
    exact floorAt_bound terrain h i (by omega)

#print axioms all_stop_flight
#print axioms terrain_terminal_optimal
end Project.Drone.Feasibility
