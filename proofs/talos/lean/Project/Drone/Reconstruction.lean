import Project.Drone.Feasibility

/-! Recover a concrete state list by following the actual stored row parents.
The public function stores those parents in a separate flat history array;
its history/loop/output-encoding correspondence is still a separate boundary. -/
namespace Project.Drone.Reconstruction
open LeanExe.Examples.Drone Optimality Selection Rows Costs Planner Feasibility

/-- Parent fields in finite rows lead to an admitted, finite predecessor and
preserve the exact natural-number cost recurrence. -/
theorem parent_step (r : Nat → UInt64) (stop : Nat → Bool) (i target : Nat)
    (hi : i ≤ 63) (hr : ∀ j, j ≤ i+1 → (r j).toNat ≤ 1000100)
    (ht : target < stateCount) (hf : (layers r stop (i+1))[3*target]! < infinity) :
    ∃ source, source < stateCount ∧ (layers r stop i)[3*source]! < infinity ∧
      (!stop (i+1) || target == 0) = true ∧
      0 < edgeTicks (r i) (r (i+1)) (altitude (r i) source) (altitude (r (i+1)) target)
        (speed source) (speed target) ∧
      (layers r stop (i+1))[3*target+2]!.toNat = source ∧
      rowCost (layers r stop (i+1)) target =
        (rowCost (layers r stop i) source).add (edgeCost r i source target) := by
  have hbound := (layers_correct r stop i (by omega) (fun j hj => hr j (by omega))).1
  change (advance (r i) (r (i+1)) (stop (i+1)) (layers r stop i))[3*target]! < infinity at hf
  rw [advance_time _ _ _ _ _ ht] at hf
  have hparent := advance_word (r i) (r (i+1)) (stop (i+1)) (layers r stop i) target 2 ht (by decide)
  change (advance _ _ _ _)[3*target+2]! = (entry (r i) (r (i+1)) (stop (i+1)) (layers r stop i) target).parent at hparent
  have hcost := advance_cost (r i) (r (i+1)) (stop (i+1)) (layers r stop i) target ht
  unfold entry at hf hparent hcost
  split at hf
  · rename_i hall
    rw [if_pos hall] at hparent hcost
    obtain ⟨source, hs, hold, hedge, hp, htime, hexcess, _, _⟩ :=
      best_parent i (layers r stop i) hbound hi (r i) (r (i+1))
        (hr i (by omega)) (hr (i+1) (by omega)) target ht hf
    refine ⟨source, hs, hold, hall, hedge, ?_, ?_⟩
    · change (advance _ _ _ _)[3*target+2]!.toNat = source
      rw [hparent, hp]
    · change rowCost (advance _ _ _ _) target = _
      rw [hcost]
      simp only [cost, rowCost, edgeCost, Cost.add, htime, hexcess]
  · simp [unreachable] at hf

/-- Backtracking uses the parent words selected by the executable row solver. -/
def backtrack (r : Nat → UInt64) (stop : Nat → Bool) : Nat → Nat → List Nat
  | 0, state => [state]
  | i+1, state =>
    backtrack r stop i (layers r stop (i+1))[3*state+2]!.toNat ++ [state]

inductive Route (r : Nat → UInt64) (stop : Nat → Bool) : Nat → Nat → Cost → List Nat → Prop
  | start : Route r stop 0 0 Cost.zero [0]
  | step {i source target : Nat} {c : Cost} {states : List Nat} :
      Route r stop i source c states → target < stateCount →
      (!stop (i+1) || target == 0) = true →
      0 < edgeTicks (r i) (r (i+1)) (altitude (r i) source) (altitude (r (i+1)) target)
        (speed source) (speed target) →
      Route r stop (i+1) target (c.add (edgeCost r i source target)) (states ++ [target])

theorem Route.flight {r stop n state c states} (route : Route r stop n state c states) :
    Flight r stop n state c := by
  induction route with
  | start => exact Flight.start
  | step _ ht ha he ih => exact Flight.step ih ht ha he

theorem Route.length {r stop n state c states} (route : Route r stop n state c states) :
    states.length = n+1 := by
  induction route with
  | start => rfl
  | step _ _ _ _ ih => simp [ih]

theorem Route.states_bounded {r stop n state c states} (route : Route r stop n state c states) :
    ∀ x ∈ states, x < stateCount := by
  induction route with
  | start => simp [stateCount]
  | @step i source target c states previous ht ha he ih =>
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih x hx
    · exact ht

/-- Following the stored parent words reconstructs a feasible route attaining
its label, with no parent-index fallback along the reference row sequence. -/
theorem backtrack_correct (r : Nat → UInt64) (stop : Nat → Bool) (n state : Nat)
    (hn : n ≤ 64) (hr : ∀ j, j ≤ n → (r j).toNat ≤ 1000100)
    (hs : state < stateCount) (hf : (layers r stop n)[3*state]! < infinity) :
    Route r stop n state (rowCost (layers r stop n) state) (backtrack r stop n state) := by
  induction n generalizing state with
  | zero =>
    have hstate := (Initial.initial_finite state hs).mp hf
    subst state
    have h := Initial.initial_fields 0 (by decide)
    simp only [ite_true, Nat.mul_zero, Nat.zero_add] at h
    have hc : rowCost (layers r stop 0) 0 = Cost.zero := by
      simp [layers, rowCost, Cost.zero, h.1, h.2.1]
    rw [hc]
    exact Route.start
  | succ i ih =>
    obtain ⟨source, hsource, hfinite, hall, hedge, hp, hc⟩ := parent_step r stop i state (by omega) hr hs hf
    rw [hc, backtrack, hp]
    exact Route.step (ih source (by omega) (fun j hj => hr j (by omega)) hsource hfinite) hs hall hedge

/-- The concrete parent-selected terminal state list is globally optimal. -/
theorem reconstructed_optimal (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat)
    (hn : n ≤ 64) (hr : ∀ j, j ≤ n → (r j).toNat ≤ 1000100) :
    Route r stop n 0 (rowCost (layers r stop n) 0) (backtrack r stop n 0) ∧
    (backtrack r stop n 0).length = n+1 ∧
    ∀ other, Flight r stop n 0 other → (rowCost (layers r stop n) 0).LE other := by
  have hroute := backtrack_correct r stop n 0 hn hr (by decide) (terminal_finite r stop n hn hr)
  exact ⟨hroute, hroute.length, (terminal_optimal r stop n hn hr).2⟩

#print axioms parent_step
#print axioms backtrack_correct
#print axioms reconstructed_optimal
end Project.Drone.Reconstruction
