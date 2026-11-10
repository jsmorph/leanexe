import Demos.Rcv.Maine.Rounds
import Demos.Rcv.Maine.Variants
import Demos.Rcv.PrintProof
import Demos.Rcv.Holder

/-!
T3 of [the requirements](requirements.md), section "Theorems", for the Maine count: (a) the count
names a winner exactly when `K` is not empty, (b) a winner of the initial test is ranked first alone
on more than half of the ballots, and when the last round has a continuing ballot the winner holds
more than half of them, (c) a last round after round 1 has one continuing candidate exactly when the
round before it was a tie of two, which the report marks, and (d) the count has no rounds exactly
when the initial test elects, and otherwise at most the larger of 1 and the size of `K` rounds.

`decision_single` shows that every elimination of `decision` names one candidate, so that a round
of two or more candidates leaves a continuing candidate (`trace_winner_iff`).  `round_facts` and
`count_winner` give the facts about the rounds and the winner that the report's printer needs:
each round's votes list an increasing set of candidates from 1 to `n`, its elimination names such
candidates, and the winner is one of them.
-/

namespace Demos.Rcv.Maine

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Stability Demos.Rcv.PrintProgram

variable {kinds : List Kind} {order : List Nat} {ballots : List (List UInt64)}

/-! ## The initial test -/

/-- `f(w)` of a candidate `w`: the number of ballots whose first position is single and marks
`w`. -/
def firstCount (ballots : List (List UInt64)) (w : Nat) : Nat :=
  (ballots.map firstPosition).count (.single w)

theorem firstCounts_eq (kinds : List Kind) (ballots : List (List UInt64)) :
    firstCounts kinds ballots = (countedSet kinds).map fun i => (i, firstCount ballots i) := rfl

/-- The initial test elects a candidate of `K` that is ranked first alone on more than half of the
ballots. -/
theorem initialWinner_spec {w : Nat} (h : initialWinner kinds ballots = some w) :
    w ∈ countedSet kinds ∧ ballots.length < 2 * firstCount ballots w := by
  unfold initialWinner at h
  rw [firstCounts_eq] at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some hx
  have hm := List.mem_of_find?_eq_some hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  exact ⟨hi, by simpa using hp⟩

/-! ## Eliminations -/

/-- Every elimination of `decision` names one candidate. -/
theorem decision_single {t : Tally} {e : Elimination} (h : decision order t = .eliminate e) :
    ∃ i, e.eliminated = [i] := by
  rcases decision_eq_eliminate h with ⟨-, hl⟩ | ⟨x, y, -, -, rfl⟩
  · unfold lowestDecision at hl
    split at hl
    · injection hl with hl
      subst hl
      exact ⟨_, rfl⟩
    · injection hl with hl
      subst hl
      exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The candidates that an elimination of `decision` names are members of the round's continuing
set, in increasing order. -/
theorem elimOk_of_decision {t : Tally} {e : Elimination} {n : Nat}
    (hS : (t.votes.map fun x : Nat × Nat => x.1).Sublist (List.range' 1 n))
    (h : decision order t = .eliminate e) : ElimOk n (some e) := by
  rcases decision_eq_eliminate h with ⟨hl, hd⟩ | ⟨x, y, hv, -, rfl⟩
  · have hne : t.votes ≠ [] := fun hnil => by simp [hnil] at hl
    have hsub : (ruleTied t.votes).Sublist (List.range' 1 n) :=
      (List.filter_sublist.map _).trans hS
    have hZne : ruleTied t.votes ≠ [] := by
      rw [ruleTied_eq_fewest]
      exact fewest_ne_nil hne
    unfold lowestDecision at hd
    split at hd
    · rename_i z hz
      injection hd with hd
      subst hd
      show [z].Sublist (List.range' 1 n)
      rw [← hz]
      exact hsub
    · injection hd with hd
      subst hd
      exact ⟨hsub, List.singleton_sublist.mpr (hsub.subset (latest_mem hZne))⟩
  · rw [hv] at hS
    exact ⟨hS, List.singleton_sublist.mpr (hS.subset (latest_mem (by simp)))⟩

/-! ## The rounds and the winner -/

theorem rounds_of_initial {w : Nat} (h : initialWinner kinds ballots = some w) :
    (count kinds order ballots).rounds = [] := by
  rw [count_initial h]

/-- The rounds of the count of `n` candidates: each holds the votes of its continuing set, a set of
candidates from 1 to `n` in increasing order, and names in its elimination only such candidates. -/
theorem round_facts (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    ∀ rd ∈ (count kinds order ballots).rounds, ∃ S : List Nat,
      rd.tally.votes = S.map (fun i => (i, (ballots.map (interpret kinds S)).count (.counts i))) ∧
      S.Sublist (List.range' 1 kinds.length) ∧ ElimOk kinds.length rd.elimination ∧
      rd.tally.continuing ≤ ballots.length ∧ rd.tally.blank ≤ ballots.length ∧
      rd.tally.uncounted ≤ ballots.length ∧ rd.tally.overvote ≤ ballots.length ∧
      rd.tally.exhausted ≤ ballots.length := by
  intro rd hrd
  cases hi : initialWinner kinds ballots with
  | some w =>
    rw [rounds_of_initial hi] at hrd
    simp at hrd
  | none =>
  obtain ⟨htally, hsub, helim⟩ := (count_trace (order := order) hi).mem rd hrd
  have hS : (continuingSet rd).Sublist (List.range' 1 kinds.length) :=
    hsub.trans (countedSet_sublist kinds)
  have hnd : (continuingSet rd).Nodup := (List.Pairwise.sublist hS List.pairwise_lt_range').nodup
  refine ⟨continuingSet rd, ?_, hS, ?_, ?_⟩
  · rw [htally]
    rfl
  · cases he : rd.elimination with
    | none => trivial
    | some e =>
      have hkeys : (rd.tally.votes.map fun x : Nat × Nat => x.1) = continuingSet rd := rfl
      exact elimOk_of_decision (by rw [hkeys]; exact hS) (helim e he)
  · have hsum := tally_sum (interpret kinds) (continuingSet rd) ballots hnd
      (fun ps i h => interpret_counts h)
    rw [← htally] at hsum
    have : rd.tally.continuing = (rd.tally.votes.map fun x : Nat × Nat => x.2).sum := rfl
    omega

/-- The winner of the last round of a trace is a member of its first continuing set. -/
theorem trace_winner_mem {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace (interpret kinds) (decision order) ballots C rds w) :
    ∀ i, w = some i → i ∈ C := by
  induction h with
  | @last C w hr =>
    intro i hi
    have hc := decision_eq_winner hr
    rw [hi] at hc
    unfold Concludes at hc
    rcases hc with ⟨-, hw⟩ | ⟨x, hx, -, hw⟩ | ⟨x, hx, y, hy, -, ⟨-, hw⟩ | ⟨-, hw⟩⟩
    · cases hw
    · injection hw with hw
      subst hw
      have := List.mem_map_of_mem (f := fun x : Nat × Nat => x.1) hx
      rwa [tally_votes_fst] at this
    · injection hw with hw
      subst hw
      have := List.mem_map_of_mem (f := fun x : Nat × Nat => x.1) hx
      rwa [tally_votes_fst] at this
    · injection hw with hw
      subst hw
      have := List.mem_map_of_mem (f := fun x : Nat × Nat => x.1) hy
      rwa [tally_votes_fst] at this
  | @step C e rds w hr _ ih =>
    intro i hi
    exact (List.mem_filter.mp (ih i hi)).1

/-- The winner of the count is a member of `K`. -/
theorem count_winner_mem {i : Nat} (h : (count kinds order ballots).winner = some i) :
    i ∈ countedSet kinds := by
  cases hi : initialWinner kinds ballots with
  | some w =>
    rw [count_initial hi] at h
    injection h with h
    subst h
    exact (initialWinner_spec hi).1
  | none => exact trace_winner_mem (count_trace hi) i h

/-- The winner of the count of `n` candidates, when there is one, is a candidate from 1 to `n`. -/
theorem count_winner (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    (i : Nat) (h : (count kinds order ballots).winner = some i) : 1 ≤ i ∧ i ≤ kinds.length :=
  mem_countedSet (count_winner_mem h)

/-! ## T3 -/

/-- In a trace of `decision` from a set without duplicates, the count names a winner exactly when
the set is not empty. -/
theorem trace_winner_iff {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace (interpret kinds) (decision order) ballots C rds w) (hC : C.Nodup) :
    w.isSome = true ↔ C ≠ [] := by
  induction h with
  | @last C w hr =>
    have hc := decision_eq_winner hr
    have hkeys := tally_votes_fst (interpret kinds) C ballots
    unfold Concludes at hc
    rcases hc with ⟨hv, rfl⟩ | ⟨x, -, hv, rfl⟩ | ⟨x, -, y, -, hv, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · rw [hv] at hkeys
      simp [← hkeys]
    · rw [hv] at hkeys
      simp [← hkeys]
    · rw [hv] at hkeys
      simp [← hkeys]
    · rw [hv] at hkeys
      simp [← hkeys]
  | @step C e rds w hr _ ih =>
    have h2 := two_le_of_eliminate (decision_ends order) hr
    obtain ⟨i, hi⟩ := decision_single hr
    obtain ⟨y, hyC, hyi⟩ := Holder.exists_ne hC h2 i
    have hy : y ∈ C.filter fun j : Nat => decide (j ∉ e.eliminated) :=
      List.mem_filter.mpr ⟨hyC, by simp [hi, hyi]⟩
    rw [ih (List.filter_sublist.nodup hC)]
    exact iff_of_true (List.ne_nil_of_mem hy) (List.ne_nil_of_mem hyC)

/-- T3(a): the count names a winner exactly when `K` is not empty. -/
theorem winner_iff (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    (count kinds order ballots).winner.isSome = true ↔ countedSet kinds ≠ [] := by
  cases hi : initialWinner kinds ballots with
  | some w =>
    rw [count_initial hi]
    exact iff_of_true rfl (List.ne_nil_of_mem (initialWinner_spec hi).1)
  | none => exact trace_winner_iff (count_trace hi) (countedSet_nodup kinds)

/-- T3(b): a winner of the initial test is ranked first alone on more than half of the ballots, and
when the last round has a continuing ballot, the winner holds more than half of them. -/
theorem winner_majority (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    (∀ w, initialWinner kinds ballots = some w → ballots.length < 2 * firstCount ballots w) ∧
      ∀ last, (count kinds order ballots).rounds.getLast? = some last →
        0 < last.tally.continuing → ∃ w v, (count kinds order ballots).winner = some w ∧
          (w, v) ∈ last.tally.votes ∧ last.tally.continuing < 2 * v := by
  refine ⟨fun w h => (initialWinner_spec h).2, fun last hl hpos => ?_⟩
  cases hi : initialWinner kinds ballots with
  | some w =>
    rw [rounds_of_initial hi] at hl
    simp at hl
  | none =>
    obtain ⟨last', hl', -, hw⟩ := (count_trace (order := order) hi).last_round
    rw [hl] at hl'
    injection hl' with hl'
    subst hl'
    have hc := decision_eq_winner hw
    unfold Concludes at hc
    unfold Tally.continuing at hpos ⊢
    rcases hc with ⟨hv, -⟩ | ⟨x, hx, hv, hwx⟩ | ⟨x, hx, y, hy, hv, ⟨hyx, hwx⟩ | ⟨hxy, hwx⟩⟩
    · rw [hv] at hpos
      simp at hpos
    · rw [hv] at hpos ⊢
      refine ⟨x.1, x.2, hwx, by simp, ?_⟩
      simp at hpos ⊢
      omega
    · refine ⟨x.1, x.2, hwx, hx, ?_⟩
      rw [hv]
      simp
      omega
    · refine ⟨y.1, y.2, hwx, hy, ?_⟩
      rw [hv]
      simp
      omega

/-- T3(c): a last round other than round 1 has a single continuing candidate exactly when the round
before it had two continuing candidates with equal votes, and that round's elimination is then by
order, with the two as the tied set, which the report prints as a `tie` line. -/
theorem tied_final (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {p : List Round} {prev last : Round}
    (h : (count kinds order ballots).rounds = p ++ [prev, last]) :
    ((continuingSet last).length = 1 ↔ ∃ a b v, prev.tally.votes = [(a, v), (b, v)]) ∧
      ∀ a b v, prev.tally.votes = [(a, v), (b, v)] →
        ∃ i, prev.elimination = some (.order [a, b] i) := by
  cases hi : initialWinner kinds ballots with
  | some w =>
    rw [rounds_of_initial hi] at h
    simp at h
  | none =>
  have ht := count_trace (order := order) hi
  have hsuf := trace_suffix p ht h
  obtain ⟨-, hsubC, -⟩ := ht.mem prev (by rw [h]; simp)
  have hSn : (continuingSet prev).Nodup := hsubC.nodup (countedSet_nodup kinds)
  obtain ⟨e, hpe, hlast⟩ := hsuf.next 0 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpe hlast
  obtain ⟨htally, -, hrule⟩ := hsuf.mem prev (by simp)
  have hr := hrule e hpe
  have hkeys : prev.tally.votes.map (fun x : Nat × Nat => x.1) = continuingSet prev := rfl
  -- the tied pair
  have hpair : ∀ a b v, prev.tally.votes = [(a, v), (b, v)] →
      e = .order [a, b] (latest order [a, b]) := by
    intro a b v hab
    rw [decision_two hab] at hr
    simp only [↓reduceIte] at hr
    injection hr with hr
    exact hr.symm
  refine ⟨⟨fun h1 => ?_, fun ⟨a, b, v, hab⟩ => ?_⟩, fun a b v hab => ⟨_, by
    rw [hpe, hpair a b v hab]⟩⟩
  · obtain ⟨i, hi⟩ := decision_single hr
    have h2 := two_le_of_eliminate (decision_ends order) (by rw [← htally]; exact hr)
    have hlen : (continuingSet prev).length = 2 := by
      have hmem : ∀ j ∈ e.eliminated, j ∈ continuingSet prev := by
        intro j hj
        have := ((decision_ends order).1 _ _ hr).2 j hj
        rwa [hkeys] at this
      have hiS : i ∈ continuingSet prev := hmem i (by simp [hi])
      have heq : ((continuingSet prev).filter fun j : Nat => decide (j ∉ e.eliminated)) =
          (continuingSet prev).erase i := by
        rw [hSn.erase_eq_filter, hi]
        apply List.filter_congr
        intro x _
        by_cases hx : x = i <;> simp [hx]
      rw [hlast, heq, List.length_erase_of_mem hiS] at h1
      omega
    rcases decision_eq_eliminate hr with ⟨h3, -⟩ | ⟨x, y, hv, hxy, -⟩
    · have : prev.tally.votes.length = (continuingSet prev).length := by
        rw [← hkeys, List.length_map]
      omega
    · obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      simp only at hxy
      subst hxy
      exact ⟨x1, y1, x2, hv⟩
  · have he := hpair a b v hab
    have hS2 : continuingSet prev = [a, b] := by
      rw [← hkeys, hab]
      rfl
    have hne : a ≠ b := by
      have := hSn
      rw [hS2] at this
      simpa using this
    rw [hlast, he, hS2]
    have hl := latest_mem (order := order) (Z := [a, b]) (by simp)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with hl | hl <;> simp [Elimination.eliminated, hl, hne, Ne.symm hne]

/-- T3(d): the count has no rounds exactly when the initial test elects, and otherwise at most the
larger of 1 and the size of `K` rounds. -/
theorem rounds_le (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    ((count kinds order ballots).rounds = [] ↔ (initialWinner kinds ballots).isSome = true) ∧
      (count kinds order ballots).rounds.length ≤ max 1 (countedSet kinds).length := by
  cases hi : initialWinner kinds ballots with
  | some w =>
    rw [rounds_of_initial hi]
    simp
  | none =>
    have ht := count_trace (order := order) hi
    exact ⟨iff_of_false (trace_ne_nil ht) (by simp), ht.length_le (decision_ends order)⟩

#print axioms winner_iff
#print axioms winner_majority
#print axioms tied_final
#print axioms rounds_le

end Demos.Rcv.Maine
