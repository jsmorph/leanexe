import Project.Drone.History

namespace Project.Drone.Output
open LeanExe.Examples.Drone Optimality Planner Feasibility Reconstruction History

def words (terrain : Array UInt64) : Nat → Nat → List UInt64
  | 0, state => [altitude (floorAt terrain 0) state, speed state]
  | i+1, state =>
    words terrain i (row terrain (i+1))[3*state+2]!.toNat ++
      [altitude (floorAt terrain (i+1)) state, speed state]

/-- An explicitly encoded feasible trajectory. Each step appends exactly its
altitude and horizontal speed, with the actual executable edge constraint. -/
inductive Encoded (terrain : Array UInt64) : Nat → Nat → Cost → List UInt64 → Prop
  | start : Encoded terrain 0 0 Cost.zero [floorAt terrain 0, 0]
  | step {i source target : Nat} {c : Cost} {output : List UInt64} :
      Encoded terrain i source c output → target < stateCount →
      (!stops terrain (i+1) || target == 0) = true →
      0 < edgeTicks (floorAt terrain i) (floorAt terrain (i+1))
        (altitude (floorAt terrain i) source) (altitude (floorAt terrain (i+1)) target)
        (speed source) (speed target) →
      Encoded terrain (i+1) target (c.add (edgeCost (floorAt terrain) i source target))
        (output ++ [altitude (floorAt terrain (i+1)) target, speed target])

theorem Encoded.length {terrain n state c output} (encoded : Encoded terrain n state c output) :
    output.length = 2*(n+1) := by
  induction encoded with
  | start => rfl
  | step _ _ _ _ ih => simp [ih]; omega

theorem Encoded.flight {terrain n state c output} (encoded : Encoded terrain n state c output) :
    Flight (floorAt terrain) (stops terrain) n state c := by
  induction encoded with
  | start => exact Flight.start
  | step _ ht hall hedge ih => exact Flight.step ih ht hall hedge

theorem words_encoded (terrain : Array UInt64) (n state : Nat)
    (hn : n ≤ 64) (hr : ∀ j, j ≤ n → (floorAt terrain j).toNat ≤ 1000100)
    (hs : state < stateCount) (hf : (row terrain n)[3*state]! < infinity) :
    Encoded terrain n state (rowCost (row terrain n) state) (words terrain n state) := by
  induction n generalizing state with
  | zero =>
    have hz := (Initial.initial_finite state hs).mp hf
    subst state
    have h := Initial.initial_fields 0 (by decide)
    simp only [ite_true, Nat.mul_zero, Nat.zero_add] at h
    have hc : rowCost (row terrain 0) 0 = Cost.zero := by
      simp [row, layers, rowCost, Cost.zero, h.1, h.2.1]
    rw [hc]
    simpa [words, altitude, speed] using (Encoded.start (terrain := terrain))
  | succ i ih =>
    obtain ⟨source, hsource, hfinite, hall, hedge, hp, hc⟩ :=
      parent_step (floorAt terrain) (stops terrain) i state (by omega) hr hs hf
    rw [hc, words, hp]
    exact Encoded.step (ih source (by omega) (fun j hj => hr j (by omega)) hsource hfinite) hs hall hedge

/-- The actual tail-recursive output loop implements the proved parent traversal. -/
theorem unwind_words (terrain history reversed : Array UInt64) (N n state : Nat)
    (hh : History.valid terrain N history) (hnN : n ≤ N) (hn : n ≤ 64)
    (hr : ∀ j, j ≤ n → (floorAt terrain j).toNat ≤ 1000100)
    (hs : state < stateCount) (hf : (row terrain n)[3*state]! < infinity) :
    (unwind (n+1) n state terrain history reversed).toList =
      words terrain n state ++ reversed.toList.reverse := by
  induction n generalizing state reversed with
  | zero => simp [unwind, words, Array.toList_reverse, Array.toList_push, List.reverse_append]
  | succ i ih =>
    obtain ⟨source, hsource, hfinite, hall, hedge, hp, hc⟩ :=
      parent_step (floorAt terrain) (stops terrain) i state (by omega) hr hs hf
    have hhparent := hh.2 (i+1) state (by omega) hnN hs
    simp only [Nat.add_sub_cancel] at hhparent
    rw [unwind]
    simp only [Nat.add_sub_cancel, Nat.succ_pos, ite_true]
    rw [hhparent, hp]
    rw [ih _ source (by omega) (by omega) (fun j hj => hr j (by omega)) hsource hfinite]
    simp only [words, hp, Array.toList_push, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append]

/-- The public source computation returns an encoded feasible route attaining
its DP label, and its exact tick/excess cost is globally optimal in the graph. -/
theorem compute_correct (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) :
    let n := terrain.size-1
    let chosen := rowCost (row terrain n) 0
    (compute terrain).size = 2*terrain.size ∧
    Encoded terrain n 0 chosen (compute terrain).toList ∧
    ∀ other, Flight (floorAt terrain) (stops terrain) n 0 other → chosen.LE other := by
  have hr : ∀ j, j ≤ terrain.size-1 → (floorAt terrain j).toNat ≤ 1000100 := by
    intro j hj
    exact floorAt_bound terrain h j (by omega)
  have hsize : terrain.size-1 ≤ 64 := by have := h.1; omega
  have hf := terminal_finite (floorAt terrain) (stops terrain) (terrain.size-1) hsize hr
  have hwords := unwind_words terrain
    (buildHistory (terrain.size-1) 1 terrain initial #[]) #[] (terrain.size-1) (terrain.size-1) 0
    (computed_history_valid terrain) (by omega) hsize hr (by decide) hf
  have hvalid : validHeights terrain.size terrain = true := (validHeights_iff _ _).mpr h.2
  have hcompute : (compute terrain).toList = words terrain (terrain.size-1) 0 := by
    have hn' : terrain.size-1+1 = terrain.size := by omega
    rw [hn'] at hwords
    simpa [compute, show terrain.size ≠ 0 by omega, show ¬terrain.size > 64 by have := h.1; omega,
      hvalid] using hwords
  have encoded := words_encoded terrain (terrain.size-1) 0 hsize hr (by decide) hf
  rw [← hcompute] at encoded
  refine ⟨?_, encoded, (terminal_optimal (floorAt terrain) (stops terrain) (terrain.size-1) hsize hr).2⟩
  have hlen := encoded.length
  simp only [Array.length_toList] at hlen
  omega

theorem compute_empty : compute #[] = #[] := by simp [compute]

theorem compute_invalid (terrain : Array UInt64) (h : ¬terrainBound terrain) :
    compute terrain = #[] := by
  unfold compute
  split
  · rfl
  · rename_i hsize
    split
    · rename_i hvalid
      have hh := (validHeights_iff _ _).mp hvalid
      have hn : terrain.size ≤ 64 := by simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hsize; omega
      exact False.elim (h ⟨hn, hh⟩)
    · rfl

theorem Encoded.first_pair {terrain n state c output}
    (encoded : Encoded terrain n state c output) :
    output.take 2 = [floorAt terrain 0, 0] := by
  induction encoded with
  | start => rfl
  | step previous _ _ _ ih =>
    rw [List.take_append_of_le_length (by rw [previous.length]; omega)]
    exact ih

theorem Encoded.last_pair {terrain n state c output}
    (encoded : Encoded terrain n state c output) :
    output.drop (2*n) = [altitude (floorAt terrain n) state, speed state] := by
  cases encoded with
  | start => simp [altitude, speed]
  | step previous _ _ _ =>
    rw [← previous.length]
    simp

/-- The public array begins and ends exactly on the terrain, at rest. -/
theorem compute_endpoints (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) :
    (compute terrain).toList.take 2 = [terrain[0]!, 0] ∧
    (compute terrain).toList.drop (2*(terrain.size-1)) = [terrain[terrain.size-1]!, 0] := by
  have he := (compute_correct terrain h hn).2.1
  constructor
  · simpa only [floorAt_first] using he.first_pair
  · simpa [altitude, speed, floorAt_last terrain hn] using he.last_pair

#print axioms unwind_words
#print axioms compute_correct
#print axioms compute_invalid
#print axioms compute_endpoints
end Project.Drone.Output
