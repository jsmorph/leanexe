import Project.Drone.Initial

/-! Correctness of repeated executable DP row transitions. The separate
compute/history/reconstruction bridge must connect the public array result to
these rows. The graph here uses precisely the executable state and edge costs. -/
namespace Project.Drone.Planner
open LeanExe.Examples.Drone Optimality Selection Rows Costs Initial

def edgeCost (r : Nat → UInt64) (i source target : Nat) : Cost :=
  ⟨(edgeTicks (r i) (r (i+1)) (altitude (r i) source) (altitude (r (i+1)) target)
    (speed source) (speed target)).toNat, (target/5)*25⟩

def rowCost (row : Array UInt64) (state : Nat) : Cost :=
  ⟨row[3*state]!.toNat, row[3*state+1]!.toNat⟩

inductive Flight (r : Nat → UInt64) (stop : Nat → Bool) : Nat → Nat → Cost → Prop
  | start : Flight r stop 0 0 Cost.zero
  | step {i source target : Nat} {c : Cost} :
      Flight r stop i source c → target < stateCount →
      (!stop (i+1) || target == 0) = true →
      0 < edgeTicks (r i) (r (i+1)) (altitude (r i) source) (altitude (r (i+1)) target)
        (speed source) (speed target) →
      Flight r stop (i+1) target (c.add (edgeCost r i source target))

theorem Flight.state_bound {r stop i state c} (flight : Flight r stop i state c) : state < stateCount := by
  cases flight with
  | start => decide
  | step _ hs _ _ => exact hs

def correct (r : Nat → UInt64) (stop : Nat → Bool) (i : Nat) (row : Array UInt64) : Prop :=
  rowBound i row ∧
  (∀ state, state < stateCount → row[3*state]! < infinity → Flight r stop i state (rowCost row state)) ∧
  (∀ state c, Flight r stop i state c → row[3*state]! < infinity ∧ (rowCost row state).LE c)

theorem advance_cost (r0 r1 : UInt64) (last : Bool) (previous : Array UInt64)
    (target : Nat) (ht : target < stateCount) :
    rowCost (advance r0 r1 last previous) target = cost (entry r0 r1 last previous target) := by
  have ht0 := advance_word r0 r1 last previous target 0 ht (by decide)
  have ht1 := advance_word r0 r1 last previous target 1 ht (by decide)
  change (advance r0 r1 last previous)[3*target+0]! = (entry r0 r1 last previous target).time at ht0
  change (advance r0 r1 last previous)[3*target+1]! = (entry r0 r1 last previous target).excess at ht1
  simp only [Nat.add_zero] at ht0
  simp only [rowCost, cost, ht0, ht1]

theorem advance_time (r0 r1 : UInt64) (last : Bool) (previous : Array UInt64)
    (target : Nat) (ht : target < stateCount) :
    (advance r0 r1 last previous)[3*target]! = (entry r0 r1 last previous target).time := by
  simpa only [word, Nat.add_zero, ite_true] using advance_word r0 r1 last previous target 0 ht (by decide)

/-- Bellman's invariant is true of the actual initial array. -/
theorem initial_correct (r : Nat → UInt64) (stop : Nat → Bool) : correct r stop 0 initial := by
  refine ⟨initial_bound, ?_, ?_⟩
  · intro state hs hf
    have heq := (initial_finite state hs).mp hf
    subst state
    have h := initial_fields 0 (by decide)
    simp only [ite_true, Nat.mul_zero, Nat.zero_add] at h
    have hc : rowCost initial 0 = Cost.zero := by simp [rowCost, Cost.zero, h.1, h.2.1]
    rw [hc]
    exact Flight.start
  · intro state c path
    cases path
    have h := initial_fields 0 (by decide)
    simp only [ite_true, Nat.mul_zero, Nat.zero_add] at h
    refine ⟨(initial_finite 0 (by decide)).mpr rfl, ?_⟩
    have hc : rowCost initial 0 = Cost.zero := by simp [rowCost, Cost.zero, h.1, h.2.1]
    rw [hc]
    exact Cost.le_refl _

/-- The actual row transition preserves feasibility and global optimality. -/
theorem advance_correct (r : Nat → UInt64) (stop : Nat → Bool) (i : Nat)
    (hi : i ≤ 63) (hr0 : (r i).toNat ≤ 1000100) (hr1 : (r (i+1)).toNat ≤ 1000100)
    (previous : Array UInt64) (hcorrect : correct r stop i previous) :
    correct r stop (i+1) (advance (r i) (r (i+1)) (stop (i+1)) previous) := by
  refine ⟨advance_bound i previous hcorrect.1 hi (r i) (r (i+1)) hr0 hr1 _, ?_, ?_⟩
  · intro target ht hfinite
    rw [advance_time _ _ _ _ _ ht] at hfinite
    rw [advance_cost _ _ _ _ _ ht]
    unfold entry at hfinite ⊢
    split at hfinite
    · rename_i hall
      rw [if_pos hall]
      obtain ⟨source, hs, hold, hedge, _, htime, hexcess, _, _⟩ :=
        best_parent i previous hcorrect.1 hi (r i) (r (i+1)) hr0 hr1 target ht hfinite
      have hc : cost (bestPredecessor stateCount (r i) (r (i+1)) previous target) =
          (rowCost previous source).add (edgeCost r i source target) := by
        simp only [cost, rowCost, edgeCost, Cost.add, htime, hexcess]
      rw [hc]
      exact Flight.step (hcorrect.2.1 source hs hold) ht hall hedge
    · simp [unreachable] at hfinite
  · intro target c path
    cases path with
    | @step _ source target c old ht hall hedge =>
      have hs := old.state_bound
      obtain ⟨hold, hle⟩ := hcorrect.2.2 source c old
      have hexact := predecessor_exact i previous hcorrect.1 hi (r i) (r (i+1)) hr0 hr1 source target hs ht hold hedge
      have hcandidate : cost (predecessor (r i) (r (i+1)) previous target source) =
          (rowCost previous source).add (edgeCost r i source target) := by
        simp only [cost, rowCost, edgeCost, Cost.add, hexact.1, hexact.2.1]
      have hminimum := scan_minimum stateCount (r i) (r (i+1)) previous target source hs
      have htime : (bestPredecessor stateCount (r i) (r (i+1)) previous target).time.toNat ≤
          (predecessor (r i) (r (i+1)) previous target source).time.toNat :=
        by simpa only [cost] using Cost.time_le hminimum
      have hfinite : (bestPredecessor stateCount (r i) (r (i+1)) previous target).time < infinity := by
        have hcf : (predecessor (r i) (r (i+1)) previous target source).time < infinity :=
          hexact.2.2.2.2.2
        rw [UInt64.lt_iff_toNat_lt] at hcf ⊢
        exact lt_of_le_of_lt htime hcf
      rw [advance_time _ _ _ _ _ ht, advance_cost _ _ _ _ _ ht]
      simp only [entry, hall, ite_true]
      refine ⟨hfinite, ?_⟩
      rw [hcandidate] at hminimum
      exact Cost.le_trans hminimum (Cost.add_mono_right hle (edgeCost r i source target))

/-- A reference sequence made exclusively of executable `advance` calls. -/
def layers (r : Nat → UInt64) (stop : Nat → Bool) : Nat → Array UInt64
  | 0 => initial
  | i+1 => advance (r i) (r (i+1)) (stop (i+1)) (layers r stop i)

theorem layers_correct (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat)
    (hn : n ≤ 64) (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100) :
    correct r stop n (layers r stop n) := by
  induction n with
  | zero => exact initial_correct r stop
  | succ n ih =>
    exact advance_correct r stop n (by omega) (hr n (by omega)) (hr (n+1) (by omega)) _
      (ih (by omega) (fun i hi => hr i (by omega)))

/-- Every finite row label is the cost of a feasible globally optimal prefix. -/
theorem layers_optimal (r : Nat → UInt64) (stop : Nat → Bool) (n state : Nat)
    (hn : n ≤ 64) (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100)
    (hs : state < stateCount) (hfinite : (layers r stop n)[3*state]! < infinity) :
    Flight r stop n state (rowCost (layers r stop n) state) ∧
    ∀ other, Flight r stop n state other → (rowCost (layers r stop n) state).LE other := by
  have h := layers_correct r stop n hn hr
  exact ⟨h.2.1 state hs hfinite, fun other path => (h.2.2 state other path).2⟩

#print axioms advance_correct
#print axioms layers_optimal
end Project.Drone.Planner
