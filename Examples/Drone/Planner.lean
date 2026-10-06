import Examples.Drone.Costs

/-! Bellman's invariant for the rows of `advance`: every finite choice is the cost of a flight
to its state, and no flight to a state costs less.  `layers` is the sequence of rows that
`advance` builds from `initial`. -/

namespace Examples.Drone.Planner

open Examples.Drone Optimality Selection Costs

/-- The cost of the edge from `source` at station `i` to `target` at station `i + 1`. -/
def edgeCost (r : Nat → UInt64) (i : Nat) (source target : UInt64) : Cost :=
  ⟨(edgeTicks (r i) (r (i + 1)) (altitude (r i) source) (altitude (r (i + 1)) target)
    (speed source) (speed target)).toNat, target.toNat / 5 * 25⟩

def rowCost (row : Array Choice) (state : UInt64) : Cost := cost row[state.toNat]!

/-- A flight from state 0 at station 0 through admitted edges, with its cost.  At a station
where `stop` holds, only state 0 is allowed. -/
inductive Flight (r : Nat → UInt64) (stop : Nat → Bool) : Nat → UInt64 → Cost → Prop
  | start : Flight r stop 0 0 Cost.zero
  | step {i : Nat} {source target : UInt64} {c : Cost} :
      Flight r stop i source c → target.toNat < 45 →
      (!stop (i + 1) || target == 0) = true →
      0 < edgeTicks (r i) (r (i + 1)) (altitude (r i) source) (altitude (r (i + 1)) target)
        (speed source) (speed target) →
      Flight r stop (i + 1) target (c.add (edgeCost r i source target))

theorem Flight.state_bound {r stop i state c} (flight : Flight r stop i state c) :
    state.toNat < 45 := by
  cases flight with
  | start => decide
  | step _ hs _ _ => exact hs

/-- The row of station `i` labels every reachable state with its least cost, and only those. -/
def correct (r : Nat → UInt64) (stop : Nat → Bool) (i : Nat) (row : Array Choice) : Prop :=
  rowBound i row ∧
  (∀ state : UInt64, state.toNat < 45 → row[state.toNat]!.time < infinity →
    Flight r stop i state (rowCost row state)) ∧
  (∀ state c, Flight r stop i state c →
    row[state.toNat]!.time < infinity ∧ (rowCost row state).LE c)

theorem initial_correct (r : Nat → UInt64) (stop : Nat → Bool) : correct r stop 0 initial := by
  have hc : rowCost initial 0 = Cost.zero := by
    simp only [rowCost, initial_zero, cost, Cost.zero]
    rfl
  refine ⟨initial_bound, fun state hs hf => ?_, fun state c path => ?_⟩
  · have h := (initial_finite state hs).mp hf
    subst h
    rw [hc]
    exact Flight.start
  · cases path
    refine ⟨(initial_finite 0 (by decide)).mpr rfl, ?_⟩
    rw [hc]
    exact Cost.le_refl _

theorem sourceCount_all {last : Bool} {target : UInt64} (h : (!last || target == 0) = true) :
    sourceCount last target = 45 := by
  simp [sourceCount, h]

theorem sourceCount_none {last : Bool} {target : UInt64} (h : ¬(!last || target == 0) = true) :
    sourceCount last target = 0 := by
  unfold sourceCount
  rw [if_neg h]

/-- An advance of a correct row is correct at the next station. -/
theorem advance_correct (r : Nat → UInt64) (stop : Nat → Bool) (i : Nat) (hi : i ≤ 63)
    (hr0 : (r i).toNat ≤ 1000100) (hr1 : (r (i + 1)).toNat ≤ 1000100)
    (previous : Array Choice) (hcorrect : correct r stop i previous) :
    correct r stop (i + 1) (advance (r i) (r (i + 1)) (stop (i + 1)) previous 0) := by
  refine ⟨advance_bound i previous hcorrect.1 hi (r i) (r (i + 1)) hr0 hr1 _,
    fun target ht hfinite => ?_, fun target c path => ?_⟩
  · rw [advance_get _ _ _ _ _ _ ht] at hfinite
    rw [rowCost, advance_get _ _ _ _ _ _ ht]
    by_cases hall : (!stop (i + 1) || target == 0) = true
    · rw [sourceCount_all hall] at hfinite ⊢
      obtain ⟨source, hs, hold, hedge, _, htime, hexcess, _, _⟩ :=
        best_parent i previous hcorrect.1 hi (r i) (r (i + 1)) hr0 hr1 target 45 ht (by decide)
          hfinite
      have hc : cost (best (r i) (r (i + 1)) previous 0 target 45) =
          (rowCost previous source).add (edgeCost r i source target) := by
        simp only [cost, rowCost, edgeCost, Cost.add, htime, hexcess]
      rw [hc]
      exact Flight.step (hcorrect.2.1 source (by simpa using hs) hold) ht hall hedge
    · rw [sourceCount_none hall] at hfinite
      have h := (best_scanned (r i) (r (i + 1)) previous 0 target 0).2.2
      rcases h with h | ⟨_, hs, _⟩
      · rw [h] at hfinite; simp at hfinite
      · simp at hs
  · cases path with
    | @step _ source target c old ht hall hedge =>
      have hs := old.state_bound
      obtain ⟨hold, hle⟩ := hcorrect.2.2 source c old
      have hexact := predecessor_exact i previous hcorrect.1 hi (r i) (r (i + 1)) hr0 hr1 source
        target hs ht hold hedge
      have hcandidate : cost (predecessor (r i) (r (i + 1)) previous[source.toNat]! target source) =
          (rowCost previous source).add (edgeCost r i source target) := by
        simp only [cost, rowCost, edgeCost, Cost.add, hexact.1, hexact.2.1]
      have hminimum := scan_minimum (r i) (r (i + 1)) previous 0 target 45 source (by simpa using hs)
      simp only [UInt64.zero_add] at hminimum
      have htime : (best (r i) (r (i + 1)) previous 0 target 45).time.toNat ≤
          (predecessor (r i) (r (i + 1)) previous[source.toNat]! target source).time.toNat := by
        simpa only [cost] using Cost.time_le hminimum
      have hfinite : (best (r i) (r (i + 1)) previous 0 target 45).time < infinity := by
        have hcf := hexact.2.2.2.2.2
        rw [UInt64.lt_iff_toNat_lt] at hcf ⊢
        exact lt_of_le_of_lt htime hcf
      rw [rowCost, advance_get _ _ _ _ _ _ ht, sourceCount_all hall]
      refine ⟨hfinite, ?_⟩
      rw [hcandidate] at hminimum
      exact Cost.le_trans hminimum (Cost.add_mono_right hle (edgeCost r i source target))

/-- The rows that `advance` builds from `initial`. -/
def layers (r : Nat → UInt64) (stop : Nat → Bool) : Nat → Array Choice
  | 0 => initial
  | i + 1 => advance (r i) (r (i + 1)) (stop (i + 1)) (layers r stop i) 0

theorem layers_correct (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat) (hn : n ≤ 64)
    (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100) : correct r stop n (layers r stop n) := by
  induction n with
  | zero => exact initial_correct r stop
  | succ n ih =>
    exact advance_correct r stop n (by omega) (hr n (by omega)) (hr (n + 1) (by omega)) _
      (ih (by omega) fun i hi => hr i (by omega))

/-- Every finite label of a row is the cost of a flight to its state, and no flight to that state
costs less. -/
theorem layers_optimal (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat) (state : UInt64)
    (hn : n ≤ 64) (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100) (hs : state.toNat < 45)
    (hfinite : (layers r stop n)[state.toNat]!.time < infinity) :
    Flight r stop n state (rowCost (layers r stop n) state) ∧
    ∀ other, Flight r stop n state other → (rowCost (layers r stop n) state).LE other := by
  have h := layers_correct r stop n hn hr
  exact ⟨h.2.1 state hs hfinite, fun other path => (h.2.2 state other path).2⟩

end Examples.Drone.Planner
