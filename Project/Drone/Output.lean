import Project.Drone.Forward

/-! The output of `compute`: the stopped final state is reachable, the parents in the table lead
back along an admitted flight that attains the least cost, and `compute` returns the altitude and
speed of each station on that flight. -/

namespace Project.Drone.Output

open LeanExe.Examples.Drone Arithmetic Timing Optimality Selection Costs Planner Forward

/-- Every bounded sequence of floors has a flight that stops at every station. -/
theorem all_stop_flight (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat)
    (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100) : ∃ c, Flight r stop n 0 c := by
  induction n with
  | zero => exact ⟨Cost.zero, Flight.start⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih fun i hi => hr i (by omega)
    have hn : (r n).toNat ≤ heightLimit := by
      have := hr n (by omega); unfold heightLimit; omega
    have hn1 : (r (n + 1)).toNat ≤ heightLimit := by
      have := hr (n + 1) (by omega); unfold heightLimit; omega
    have hedge := (rest_admitted (r n) (r (n + 1)) (r n) (r (n + 1)) hn hn1).1
    refine ⟨c.add (edgeCost r n 0 0), Flight.step hc (by decide) (by simp) ?_⟩
    simpa [altitude, speed] using hedge

/-- The stopped state of the last station is reachable. -/
theorem terminal_finite (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat) (hn : n ≤ 64)
    (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100) :
    (layers r stop n)[(0 : UInt64).toNat]!.time < infinity := by
  obtain ⟨c, hc⟩ := all_stop_flight r stop n hr
  exact ((layers_correct r stop n hn hr).2.2 0 c hc).1

/-- The label of the stopped final state is the cost of a flight, and no flight to it costs
less. -/
theorem terminal_optimal (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat) (hn : n ≤ 64)
    (hr : ∀ i, i ≤ n → (r i).toNat ≤ 1000100) :
    Flight r stop n 0 (rowCost (layers r stop n) 0) ∧
    ∀ other, Flight r stop n 0 other → (rowCost (layers r stop n) 0).LE other :=
  layers_optimal r stop n 0 hn hr (by decide) (terminal_finite r stop n hn hr)

/-- Every parent in a row is a state. -/
theorem layers_parent (r : Nat → UInt64) (stop : Nat → Bool) (m : Nat) (s : UInt64)
    (hs : s.toNat < 45) : (layers r stop m)[s.toNat]!.parent.toNat < 45 := by
  cases m with
  | zero =>
    simp only [layers]
    rw [initial_get s hs]
    simp [initialChoice]
  | succ m =>
    simp only [layers]
    rw [advance_get _ _ _ _ _ _ hs]
    rcases (best_scanned (r m) (r (m + 1)) (layers r stop m) 0 s
      (sourceCount (stop (m + 1)) s)).2.2 with h | ⟨source, hsrc, h⟩
    · rw [h]; decide
    · rw [h]
      have hle := sourceCount_le (stop (m + 1)) s
      unfold candidate predecessor
      simp only
      split
      · simp only; omega
      · decide

/-- A finite label of a row comes from its parent in the row before, through an admitted edge,
with the parent's label plus the edge's cost. -/
theorem parent_step (r : Nat → UInt64) (stop : Nat → Bool) (i : Nat) (target : UInt64)
    (hi : i ≤ 63) (hr : ∀ j, j ≤ i + 1 → (r j).toNat ≤ 1000100) (ht : target.toNat < 45)
    (hf : (layers r stop (i + 1))[target.toNat]!.time < infinity) :
    ∃ source : UInt64, source.toNat < 45 ∧ (layers r stop i)[source.toNat]!.time < infinity ∧
      (!stop (i + 1) || target == 0) = true ∧
      0 < edgeTicks (r i) (r (i + 1)) (altitude (r i) source) (altitude (r (i + 1)) target)
        (speed source) (speed target) ∧
      (layers r stop (i + 1))[target.toNat]!.parent = source ∧
      rowCost (layers r stop (i + 1)) target =
        (rowCost (layers r stop i) source).add (edgeCost r i source target) := by
  have hbound := (layers_correct r stop i (by omega) fun j hj => hr j (by omega)).1
  simp only [layers] at hf ⊢
  rw [advance_get _ _ _ _ _ _ ht] at hf ⊢
  by_cases hall : (!stop (i + 1) || target == 0) = true
  · rw [sourceCount_all hall] at hf ⊢
    obtain ⟨source, hs, hold, hedge, hp, htime, hexcess, _, _⟩ :=
      best_parent i (layers r stop i) hbound hi (r i) (r (i + 1)) (hr i (by omega))
        (hr (i + 1) (by omega)) target 45 ht (by decide) hf
    refine ⟨source, by simpa using hs, hold, hall, hedge, hp, ?_⟩
    simp only [rowCost, advance_get _ _ _ _ _ _ ht, sourceCount_all hall, cost, edgeCost,
      Cost.add, htime, hexcess]
  · rw [sourceCount_none hall] at hf
    rcases (best_scanned (r i) (r (i + 1)) (layers r stop i) 0 target 0).2.2 with h | ⟨_, hs, _⟩
    · rw [h] at hf; simp at hf
    · simp at hs

/-- The words of the flight that ends in `state` at station `n`, following the parents back:
the altitude and the speed at each station. -/
def words (r : Nat → UInt64) (stop : Nat → Bool) : Nat → UInt64 → List UInt64
  | 0, state => [altitude (r 0) state, speed state]
  | i + 1, state => words r stop i (layers r stop (i + 1))[state.toNat]!.parent ++
      [altitude (r (i + 1)) state, speed state]

/-- An admitted flight with its cost, each station adding its altitude and speed. -/
inductive Encoded (r : Nat → UInt64) (stop : Nat → Bool) : Nat → UInt64 → Cost →
    List UInt64 → Prop
  | start : Encoded r stop 0 0 Cost.zero [r 0, 0]
  | step {i : Nat} {source target : UInt64} {c : Cost} {output : List UInt64} :
      Encoded r stop i source c output → target.toNat < 45 →
      (!stop (i + 1) || target == 0) = true →
      0 < edgeTicks (r i) (r (i + 1)) (altitude (r i) source) (altitude (r (i + 1)) target)
        (speed source) (speed target) →
      Encoded r stop (i + 1) target (c.add (edgeCost r i source target))
        (output ++ [altitude (r (i + 1)) target, speed target])

theorem Encoded.length {r stop n state c output} (encoded : Encoded r stop n state c output) :
    output.length = 2 * (n + 1) := by
  induction encoded with
  | start => rfl
  | step _ _ _ _ ih => simp [ih]; omega

theorem Encoded.flight {r stop n state c output} (encoded : Encoded r stop n state c output) :
    Flight r stop n state c := by
  induction encoded with
  | start => exact Flight.start
  | step _ ht hall hedge ih => exact Flight.step ih ht hall hedge

/-- The words along the parents encode an admitted flight that attains the label. -/
theorem words_encoded (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat) (state : UInt64)
    (hn : n ≤ 64) (hr : ∀ j, j ≤ n → (r j).toNat ≤ 1000100) (hs : state.toNat < 45)
    (hf : (layers r stop n)[state.toNat]!.time < infinity) :
    Encoded r stop n state (rowCost (layers r stop n) state) (words r stop n state) := by
  induction n generalizing state with
  | zero =>
    have hz := (initial_finite state hs).mp hf
    subst hz
    have hc : rowCost (layers r stop 0) 0 = Cost.zero := by
      simp only [layers, rowCost, initial_zero, cost, Cost.zero]; rfl
    rw [hc]
    simpa [words, altitude, speed] using (Encoded.start (r := r) (stop := stop))
  | succ i ih =>
    obtain ⟨source, hsource, hfinite, hall, hedge, hp, hc⟩ :=
      parent_step r stop i state (by omega) hr hs hf
    rw [hc, words, hp]
    exact Encoded.step (ih source (by omega) (fun j hj => hr j (by omega)) hsource hfinite) hs
      hall hedge

/-- The state at station `n - j` on the flight that ends in `state` at station `n`. -/
def chain (r : Nat → UInt64) (stop : Nat → Bool) : Nat → UInt64 → Nat → UInt64
  | _, state, 0 => state
  | n, state, j + 1 => chain r stop (n - 1) (layers r stop n)[state.toNat]!.parent j

theorem chain_last (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat) (state : UInt64) (j : Nat) :
    chain r stop n state (j + 1) =
      (layers r stop (n - j))[(chain r stop n state j).toNat]!.parent := by
  induction j generalizing n state with
  | zero => simp [chain]
  | succ j ih =>
    rw [chain, ih, chain]
    congr 3
    omega

theorem words_length (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat) (state : UInt64) :
    (words r stop n state).length = 2 * (n + 1) := by
  induction n generalizing state with
  | zero => rfl
  | succ i ih => simp [words, ih]; omega

/-- Word `2 k + b` of the flight is the altitude, for `b = 0`, or the speed, for `b = 1`, at
station `k`. -/
theorem words_get (r : Nat → UInt64) (stop : Nat → Bool) (n : Nat) (state : UInt64) (k : Nat)
    (hk : k ≤ n) :
    (words r stop n state)[2 * k]! = altitude (r k) (chain r stop n state (n - k)) ∧
    (words r stop n state)[2 * k + 1]! = speed (chain r stop n state (n - k)) := by
  induction n generalizing state with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp [words, chain]
  | succ i ih =>
    by_cases hki : k ≤ i
    · have hlen := words_length r stop i (layers r stop (i + 1))[state.toNat]!.parent
      have h := ih (layers r stop (i + 1))[state.toNat]!.parent hki
      have hchain : chain r stop (i + 1) state (i + 1 - k) =
          chain r stop i (layers r stop (i + 1))[state.toNat]!.parent (i - k) := by
        rw [show i + 1 - k = (i - k) + 1 by omega, chain]
        rfl
      rw [hchain, words]
      refine ⟨?_, ?_⟩
      · rw [getElem!_pos _ _ (by simp [hlen]; omega), List.getElem_append_left (by omega),
          ← getElem!_pos _ _ (by omega)]
        exact h.1
      · rw [getElem!_pos _ _ (by simp [hlen]; omega), List.getElem_append_left (by omega),
          ← getElem!_pos _ _ (by omega)]
        exact h.2
    · obtain rfl : k = i + 1 := by omega
      have hlen := words_length r stop i (layers r stop (i + 1))[state.toNat]!.parent
      simp only [Nat.sub_self, chain, words]
      refine ⟨?_, ?_⟩
      · rw [getElem!_pos _ _ (by simp [hlen]), List.getElem_append_right (by omega)]
        simp [hlen]
      · rw [getElem!_pos _ _ (by simp [hlen]), List.getElem_append_right (by omega)]
        simp [hlen]

end Project.Drone.Output
