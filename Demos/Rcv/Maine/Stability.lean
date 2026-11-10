import Demos.Rcv.Maine.Spec
import Demos.Rcv.Batch

/-!
T8 of [the requirements](requirements.md), section "Theorems", for the Maine interpretation, and
T10's application to it.  `interpret_closed` states that the interpretation counts a ballot only
for a member of the continuing set, and `interpret_stable` states both statements of T8, which
`stability_counts` and `stability_inactive` give separately.  Rule 1 of the interpretation ends the
examination at a position whatever the continuing set, so the proofs follow the Oakland module's
with one more case.  With both properties, `Demos.Rcv.Batch.run_batch_winner`,
`Demos.Rcv.Batch.run_batch_rounds`, and `Demos.Rcv.Batch.run_batch_members` hold for the
interpretation, as `batch_winner`, `batch_rounds`, and `batch_members` state.
-/

namespace Demos.Rcv.Maine

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Stability Demos.Rcv.Variants

/-! ## The interpretation counts only for a continuing candidate -/

theorem examine_counts {C : List Nat} {i : Nat} :
    ∀ {ps : List UInt64}, examine C ps = some (.counts i) → i ∈ C
  | [], h => by simp [examine] at h
  | p :: ps, h => by
    cases hp : position p with
    | empty =>
      simp only [examine, hp] at h
      by_cases hs : skipped ps = true
      · rw [ite_eq_left hs] at h
        simp at h
      · rw [ite_eq_right hs] at h
        exact examine_counts h
    | multiple => simp [examine, hp] at h
    | single j =>
      simp only [examine, hp] at h
      by_cases hj : j ∈ C
      · rw [ite_eq_left hj] at h
        simp only [Option.some.injEq, Outcome.counts.injEq] at h
        exact h ▸ hj
      · rw [ite_eq_right hj] at h
        exact examine_counts h

/-- The interpretation counts a ballot only for a member of the continuing set. -/
theorem interpret_counts {kinds : List Kind} {C : List Nat} {ps : List UInt64} {i : Nat}
    (h : interpret kinds C ps = .counts i) : i ∈ C := by
  unfold interpret at h
  cases he : examine C ps with
  | none => simp [he] at h
  | some o =>
    simp only [he, Option.getD_some] at h
    subst h
    exact examine_counts he

theorem interpret_closed (kinds : List Kind) : Closed (interpret kinds) :=
  fun _ _ _ h => interpret_counts h

/-! ## T8 -/

theorem examine_counts_subset {S S' : List Nat} (hS : S' ⊆ S) {w : Nat} (hw : w ∈ S') :
    ∀ {ps : List UInt64}, examine S ps = some (.counts w) → examine S' ps = some (.counts w)
  | [], h => by simp [examine] at h
  | p :: ps, h => by
    cases hp : position p with
    | empty =>
      simp only [examine, hp] at h ⊢
      by_cases hs : skipped ps = true
      · rw [ite_eq_left hs] at h
        simp at h
      · rw [ite_eq_right hs] at h ⊢
        exact examine_counts_subset hS hw h
    | multiple => simp [examine, hp] at h
    | single i =>
      simp only [examine, hp] at h ⊢
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi] at h
        simp only [Option.some.injEq, Outcome.counts.injEq] at h
        subst h
        rw [ite_eq_left hw]
      · rw [ite_eq_right hi] at h
        rw [ite_eq_right (fun h' => hi (hS h'))]
        exact examine_counts_subset hS hw h

theorem examine_inactive_subset {S S' : List Nat} (hS : S' ⊆ S) {r : Reason} :
    ∀ {ps : List UInt64}, examine S ps = some (.inactive r) → examine S' ps = some (.inactive r)
  | [], h => by simp [examine] at h
  | p :: ps, h => by
    cases hp : position p with
    | empty =>
      simp only [examine, hp] at h ⊢
      by_cases hs : skipped ps = true
      · rw [ite_eq_left hs] at h ⊢
        exact h
      · rw [ite_eq_right hs] at h ⊢
        exact examine_inactive_subset hS h
    | multiple =>
      simp only [examine, hp] at h ⊢
      exact h
    | single i =>
      simp only [examine, hp] at h ⊢
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi] at h
        simp at h
      · rw [ite_eq_right hi] at h
        rw [ite_eq_right (fun h' => hi (hS h'))]
        exact examine_inactive_subset hS h

theorem examine_none_subset {S S' : List Nat} (hS : S' ⊆ S) :
    ∀ {ps : List UInt64}, examine S ps = none → examine S' ps = none
  | [], _ => rfl
  | p :: ps, h => by
    cases hp : position p with
    | empty =>
      simp only [examine, hp] at h ⊢
      by_cases hs : skipped ps = true
      · rw [ite_eq_left hs] at h
        simp at h
      · rw [ite_eq_right hs] at h ⊢
        exact examine_none_subset hS h
    | multiple => simp [examine, hp] at h
    | single i =>
      simp only [examine, hp] at h ⊢
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi] at h
        simp at h
      · rw [ite_eq_right hi] at h
        rw [ite_eq_right (fun h' => hi (hS h'))]
        exact examine_none_subset hS h

/-- T8, first statement: for continuing sets `S' ⊆ S`, a ballot that counts for `w` against `S`
counts for `w` against `S'` whenever `w ∈ S'`. -/
theorem stability_counts {kinds : List Kind} {S S' : List Nat} {ps : List UInt64} {w : Nat}
    (hS : S' ⊆ S) (h : interpret kinds S ps = .counts w) (hw : w ∈ S') :
    interpret kinds S' ps = .counts w := by
  unfold interpret at h ⊢
  cases he : examine S ps with
  | none =>
    rw [he] at h
    simp at h
  | some o =>
    rw [he, Option.getD_some] at h
    subst h
    rw [examine_counts_subset hS hw he, Option.getD_some]

/-- T8, second statement: for continuing sets `S' ⊆ S`, a ballot that is inactive against `S` with
a reason is inactive against `S'` with the same reason. -/
theorem stability_inactive {kinds : List Kind} {S S' : List Nat} {ps : List UInt64} {r : Reason}
    (hS : S' ⊆ S) (h : interpret kinds S ps = .inactive r) :
    interpret kinds S' ps = .inactive r := by
  unfold interpret at h ⊢
  cases he : examine S ps with
  | none =>
    rw [he, Option.getD_none] at h
    rw [examine_none_subset hS he, Option.getD_none]
    exact h
  | some o =>
    rw [he, Option.getD_some] at h
    subst h
    rw [examine_inactive_subset hS he, Option.getD_some]

theorem interpret_stable (kinds : List Kind) : Stable (interpret kinds) :=
  ⟨fun _ _ _ _ hS h hw => stability_counts hS h hw, fun _ _ _ _ hS h => stability_inactive hS h⟩

/-! ## T10 for this interpretation -/

/-- T10(a) of the Oakland module for this interpretation: from `K`, the count of the Oakland rules
and the single count, both with this interpretation, name the same winner, or both none. -/
theorem batch_winner (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    (run (interpret kinds) (ruleSingle order) ballots ((countedSet kinds).length + 1)
        (countedSet kinds)).winner =
      (run (interpret kinds) (rule order) ballots ((countedSet kinds).length + 1)
        (countedSet kinds)).winner :=
  Batch.run_batch_winner (interpret_closed kinds) (interpret_stable kinds) order ballots
    (countedSet_nodup kinds)

/-- T10(b) of the Oakland module for this interpretation. -/
theorem batch_rounds (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    let k := run (interpret kinds) (rule order) ballots ((countedSet kinds).length + 1)
      (countedSet kinds)
    let k' := run (interpret kinds) (ruleSingle order) ballots ((countedSet kinds).length + 1)
      (countedSet kinds)
    (k.rounds.map Round.tally).Sublist (k'.rounds.map Round.tally) ∨
      ((k.rounds.map Round.tally).dropLast.Sublist (k'.rounds.map Round.tally) ∧
        k'.winner = k.winner ∧
        ∃ a b, k.rounds.getLast? = some a ∧ k'.rounds.getLast? = some b ∧
          continuingSet a ⊆ continuingSet b ∧ ∃ x ∈ continuingSet b, x ∉ continuingSet a) :=
  Batch.run_batch_rounds (interpret_closed kinds) (interpret_stable kinds) order ballots
    (countedSet_nodup kinds)

/-- T10(c) of the Oakland module for this interpretation. -/
theorem batch_members (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {p q p' q' : List Round} {rd sd : Round} {B : List Nat}
    (hk : (run (interpret kinds) (rule order) ballots ((countedSet kinds).length + 1)
      (countedSet kinds)).rounds = p ++ rd :: q)
    (hrd : rd.elimination = some (.batch B))
    (hk' : (run (interpret kinds) (ruleSingle order) ballots ((countedSet kinds).length + 1)
      (countedSet kinds)).rounds = p' ++ sd :: q')
    (hset : continuingSet sd = continuingSet rd) :
    ∀ sj ∈ (sd :: q').take B.length, sj.elimination = none ∨
      ∃ b ∈ B, b ∈ continuingSet sj ∧ ∃ e, sj.elimination = some e ∧ e.eliminated = [b] :=
  Batch.run_batch_members (interpret_closed kinds) (interpret_stable kinds) order ballots
    (countedSet_nodup kinds) hk hrd hk' hset

end Demos.Rcv.Maine
