import Demos.Rcv.Rounds

/-!
The single count and the county count of [the requirements](requirements.md), section "Theorems",
with which T10 and T11 compare the count.  The single count is the count without rule 3.  The
county count, Alameda County's practice, interprets ballots as the count does, has no majority
stop, no rule 2, and no rule 3, eliminates by rule 4 while three or more candidates continue, and
ends at the first round with at most two candidates, naming the one with more votes, the candidate
alone, or none when the two tie or none continues.

Both are `Demos.Rcv.Spec.run` from the counted set with the count's interpretation and fuel and a
decision of their own.  `ruleSingle` and `ruleCounty` decide a round from its counts as
`Demos.Rcv.Spec.rule` does, with rule 4 as `Demos.Rcv.Rounds.lowestDecision` of
`Demos.Rcv.Rounds.ruleTied`, so that the three counts share the specification's tally, rules, and
tie-break.  `ruleSingle_ends` and `ruleCounty_ends` state `Demos.Rcv.Rounds.Ends` of each, so the
lemmas of `Demos/Rcv/Rounds.lean` about `run` apply to both counts.
-/

namespace Demos.Rcv.Variants

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds

/-- The rules of a round of the single count: rules 1, 2, and 4. -/
def ruleSingle (order : List Nat) (t : Tally) : Decision :=
  match t.votes.find? fun x : Nat × Nat => t.continuing < (2 : Nat) * x.2 with
  | some x => .winner (some x.1)
  | none => if t.continuing = 0 then .winner none else lowestDecision order (ruleTied t.votes)

/-- The winner of the county count's last round, whose votes are `votes`: the candidate alone, the
one of two with more votes, or none when the two tie or none continues.  The county count calls it
only for a round with at most two candidates. -/
def countyWinner : List (Nat × Nat) → Option Nat
  | [x] => some x.1
  | [x, y] => if y.2 < x.2 then some x.1 else if x.2 < y.2 then some y.1 else none
  | _ => none

/-- The rule of a round of the county count: the end of the count when at most two candidates
continue, and rule 4 otherwise. -/
def ruleCounty (order : List Nat) (t : Tally) : Decision :=
  if t.votes.length ≤ 2 then .winner (countyWinner t.votes)
  else lowestDecision order (ruleTied t.votes)

/-- The single count of a contest, from round 1 with `C₁ = K`. -/
def singleCount (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) : Count :=
  run (interpret kinds) (ruleSingle order) ballots ((countedSet kinds).length + 1)
    (countedSet kinds)

/-- The county count of a contest, from round 1 with `C₁ = K`. -/
def countyCount (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) : Count :=
  run (interpret kinds) (ruleCounty order) ballots ((countedSet kinds).length + 1)
    (countedSet kinds)

/-! ## Rule 4 -/

/-- A member of `fewest votes` has no more votes than any candidate of `votes`. -/
theorem fewest_min {votes : List (Nat × Nat)} {i : Nat} (h : i ∈ fewest votes) :
    ∃ v, (i, v) ∈ votes ∧ ∀ y ∈ votes, v ≤ y.2 := by
  unfold fewest at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  obtain ⟨hxv, hall⟩ := List.mem_filter.1 hx
  refine ⟨x.2, hxv, fun y hy => ?_⟩
  have := List.all_eq_true.1 hall y hy
  simpa using this

/-- Rule 4 eliminates one member of the nonempty set `Z`. -/
theorem lowestDecision_eliminated {order Z : List Nat} {e : Elimination} (hne : Z ≠ [])
    (h : lowestDecision order Z = .eliminate e) : ∃ z ∈ Z, e.eliminated = [z] := by
  unfold lowestDecision at h
  split at h
  · rename_i z
    injection h with h
    subst h
    exact ⟨z, by simp, rfl⟩
  · injection h with h
    subst h
    exact ⟨latest order Z, latest_mem hne, rfl⟩

/-- Rule 4 for a round with a continuing candidate eliminates one member of the tied set. -/
theorem lowest_eliminated {order : List Nat} {t : Tally} {e : Elimination} (hne : t.votes ≠ [])
    (h : lowestDecision order (ruleTied t.votes) = .eliminate e) :
    ∃ z ∈ fewest t.votes, e.eliminated = [z] := by
  rw [ruleTied_eq_fewest] at h
  exact lowestDecision_eliminated (fewest_ne_nil hne) h

theorem lowest_ends {order : List Nat} {t : Tally} {e : Elimination} (hne : t.votes ≠ [])
    (h : lowestDecision order (ruleTied t.votes) = .eliminate e) :
    e.eliminated ≠ [] ∧ ∀ i ∈ e.eliminated, i ∈ t.votes.map fun x : Nat × Nat => x.1 := by
  obtain ⟨z, hz, he⟩ := lowest_eliminated hne h
  rw [he]
  refine ⟨by simp, fun i hi => ?_⟩
  rw [List.mem_singleton.1 hi]
  exact fewest_sub hz

theorem ruleSingle_ends (order : List Nat) : Ends (ruleSingle order) := by
  refine ⟨fun t e h => ?_, fun t ht => ?_⟩
  · unfold ruleSingle at h
    split at h
    · cases h
    · by_cases h0 : t.continuing = 0
      · rw [ite_eq_left h0] at h
        cases h
      · rw [ite_eq_right h0] at h
        exact lowest_ends (votes_ne_nil (Nat.pos_of_ne_zero h0)) h
  · match hv : t.votes, ht with
    | [], _ => exact ⟨none, by simp [ruleSingle, Tally.continuing, hv]⟩
    | [x], _ =>
      by_cases hx : x.2 = 0
      · exact ⟨none, by simp [ruleSingle, Tally.continuing, hv, hx]⟩
      · have : x.2 < 2 * x.2 := by omega
        exact ⟨some x.1, by simp [ruleSingle, Tally.continuing, hv, this]⟩

theorem ruleCounty_ends (order : List Nat) : Ends (ruleCounty order) := by
  refine ⟨fun t e h => ?_, fun t ht => ⟨countyWinner t.votes, ?_⟩⟩
  · unfold ruleCounty at h
    by_cases h2 : t.votes.length ≤ 2
    · rw [ite_eq_left h2] at h
      cases h
    · rw [ite_eq_right h2] at h
      exact lowest_ends (fun hnil => by simp [hnil] at h2) h
  · unfold ruleCounty
    rw [ite_eq_left (by omega)]

end Demos.Rcv.Variants
