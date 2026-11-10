import Demos.Rcv.Holder

/-!
T3 of [the requirements](requirements.md), section "Theorems": the count names a winner exactly
when round 1 has a continuing ballot, the winner holds a majority of the last round's continuing
ballots, a last round after round 1 has one continuing candidate exactly when the round before it
was a tie of two, which the report marks, and the count has at most the larger of 1 and the size of
`K` rounds.  `next_pos` shows that a round with a continuing ballot that eliminates leaves a
candidate with votes, so that, by T8, every later round has a continuing ballot.
-/

namespace Demos.Rcv.Winner

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Stability Demos.Rcv.Variants
  Demos.Rcv.Batch Demos.Rcv.Holder

variable {interp : Interp} {ballots : List (List UInt64)}

/-- A round that eliminates leaves a continuing candidate with votes, so the next round has a
continuing ballot. -/
theorem next_pos (hS : Stable interp) {order C : List Nat} {e : Elimination}
    (hC : C.Nodup) (hr : rule order (tally interp C ballots) = .eliminate e) :
    0 < (tally interp (C.filter fun i : Nat => decide (i ∉ e.eliminated)) ballots).continuing := by
  have hC1 : (C.filter fun i : Nat => decide (i ∉ e.eliminated)).Nodup :=
    List.filter_sublist.nodup hC
  have hsub : (C.filter fun i : Nat => decide (i ∉ e.eliminated)) ⊆ C :=
    List.filter_sublist.subset
  suffices h : ∃ x ∈ C.filter (fun i : Nat => decide (i ∉ e.eliminated)),
      0 < votesFor interp C ballots x by
    obtain ⟨x, hx, hpos⟩ := h
    have := votesFor_mono hS hsub ballots hx
    have := votesFor_le_continuing interp ballots hC1 hx
    omega
  by_cases hbat : ∃ B, e = .batch B
  · obtain ⟨B, rfl⟩ := hbat
    obtain ⟨X, hb⟩ := batchAt_of_rule hC hr
    exact ⟨X, List.mem_filter.2 ⟨hb.mem, by simp [Elimination.eliminated, hb.not_mem_X]⟩,
      hb.X_pos⟩
  · have hnb : ∀ s, e ≠ .batch s := fun s h => hbat ⟨s, h⟩
    obtain ⟨hpos, -, -⟩ := rule_eq_eliminate hr
    have h2 := two_le_of_eliminate (rule_ends order) hr
    obtain ⟨z, hzC, hez, hmin⟩ := lowest_min (S := C) (by
      intro hnil
      rw [hnil] at h2
      simp at h2) (rule_lowest hr hnb)
    have hy : ∃ y ∈ C, 0 < votesFor interp C ballots y := by
      rw [continuing_eq_countP interp ballots hC] at hpos
      obtain ⟨o, ho, hco⟩ := List.countP_pos_iff.1 hpos
      cases o with
      | inactive r => simp [countsIn] at hco
      | counts y =>
        refine ⟨y, by simpa [countsIn] using hco, ?_⟩
        unfold votesFor
        exact List.count_pos_iff.2 ho
    obtain ⟨y, hyC, hy⟩ := hy
    obtain ⟨x, hxC, hxz⟩ := exists_ne hC h2 z
    by_cases hyz : y = z
    · have := hmin x hxC
      rw [hyz] at hy
      exact ⟨x, List.mem_filter.2 ⟨hxC, by simp [hez, hxz]⟩, by omega⟩
    · exact ⟨y, List.mem_filter.2 ⟨hyC, by simp [hez, hyz]⟩, hy⟩

/-- T3(a) over traces: a count from a set without duplicates names a winner exactly when its first
round has a continuing ballot. -/
theorem trace_winner_iff (hS : Stable interp) {order : List Nat} :
    ∀ {C : List Nat} {rds : List Round} {w : Option Nat},
      Trace interp (rule order) ballots C rds w → C.Nodup →
        (w.isSome = true ↔ 0 < (tally interp C ballots).continuing) := by
  intro C rds w ht
  induction ht with
  | @last C w hr =>
    intro hC
    rcases rule_eq_winner hr with ⟨x, hx, hm, rfl⟩ | ⟨h0, rfl⟩
    · obtain ⟨hi, hv⟩ := mem_votes.1 (show (x.1, x.2) ∈ (tally interp C ballots).votes from hx)
      have := votesFor_le_continuing interp ballots hC hi
      rw [← hv] at this
      simp only [Option.isSome_some, true_iff]
      omega
    · simp [h0]
  | @step C e rds w hr hrest ih =>
    intro hC
    obtain ⟨hpos, -, -⟩ := rule_eq_eliminate hr
    rw [ih (List.filter_sublist.nodup hC)]
    exact iff_of_true (next_pos hS hC hr) hpos

/-- When the round before the last round holds two candidates with equal votes, the round
eliminates by order with that pair as the tied set, and the last round has one candidate. -/
theorem trace_tie {order C : List Nat} {rds : List Round} {w : Option Nat}
    (ht : Trace interp (rule order) ballots C rds w) (hC : C.Nodup) {p : List Round}
    {prev last : Round} (h : rds = p ++ [prev, last]) {a b v : Nat}
    (hab : prev.tally.votes = [(a, v), (b, v)]) :
    (∃ i, prev.elimination = some (.order [a, b] i)) ∧ (continuingSet last).length = 1 := by
  have hsuf := trace_suffix p ht h
  obtain ⟨-, hsubC, -⟩ := ht.mem prev (by rw [h]; simp)
  have hSn : (continuingSet prev).Nodup := hsubC.nodup hC
  obtain ⟨e, hpe, hlast⟩ := hsuf.next 0 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpe hlast
  obtain ⟨htally, -, hrule⟩ := hsuf.mem prev (by simp)
  have hr := hrule e hpe
  have hS2 : continuingSet prev = [a, b] := by
    simp [continuingSet, hab]
  have hne : a ≠ b := by
    have := hSn
    rw [hS2] at this
    simpa using this
  have htied : ruleTied prev.tally.votes = [a, b] := by
    rw [ruleTied_eq_fewest, hab]
    simp [fewest]
  obtain ⟨-, -, hcases⟩ := rule_eq_eliminate hr
  rcases hcases with ⟨s, hs, rfl⟩ | ⟨-, ⟨z, hz, rfl⟩ | ⟨-, rfl⟩⟩
  · obtain ⟨hlen, ⟨x, hx, -, rfl⟩, -⟩ := batch_some hs
    rw [hab] at hx hlen
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> simp [lower] at hlen
  · rw [htied] at hz
    simp at hz
  · rw [htied] at hpe hlast
    refine ⟨⟨_, hpe⟩, ?_⟩
    rw [hlast, hS2]
    have hl := latest_mem (order := order) (Z := [a, b]) (by simp)
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with hl | hl <;> simp [Elimination.eliminated, hl, hne, Ne.symm hne]

/-! ## T3 -/

/-- T3(a): the count names a winner exactly when round 1 has a continuing ballot. -/
theorem winner_iff (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    ∃ rd, (count kinds order ballots).rounds.head? = some rd ∧
      ((count kinds order ballots).winner.isSome = true ↔ 0 < rd.tally.continuing) := by
  have ht := count_trace kinds order ballots
  obtain ⟨e0, rest, hcons⟩ := trace_cons ht
  refine ⟨_, by rw [hcons]; rfl, ?_⟩
  exact trace_winner_iff (interpret_stable kinds) ht
    (countedSet_nodup kinds)

/-- T3(b): the winner holds more than half of the continuing ballots of the last round. -/
theorem winner_majority (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {w : Nat} (h : (count kinds order ballots).winner = some w) :
    ∃ last v, (count kinds order ballots).rounds.getLast? = some last ∧
      (w, v) ∈ last.tally.votes ∧ last.tally.continuing < 2 * v :=
  trace_holder (count_trace kinds order ballots) h

/-- T3(c): a last round other than round 1 has a single continuing candidate exactly when the round
before it had two continuing candidates with equal votes, and that round's elimination is then by
order, with the two as the tied set, which the report prints as a `tie` line. -/
theorem tied_final (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {p : List Round} {prev last : Round}
    (h : (count kinds order ballots).rounds = p ++ [prev, last]) :
    ((continuingSet last).length = 1 ↔ ∃ a b v, prev.tally.votes = [(a, v), (b, v)]) ∧
      ∀ a b v, prev.tally.votes = [(a, v), (b, v)] →
        ∃ i, prev.elimination = some (.order [a, b] i) := by
  have ht := count_trace kinds order ballots
  have hC := countedSet_nodup kinds
  refine ⟨⟨trace_tied ht hC h, ?_⟩, fun a b v hab => (trace_tie ht hC h hab).1⟩
  rintro ⟨a, b, v, hab⟩
  exact (trace_tie ht hC h hab).2

/-- T3(d): the count has at most the larger of 1 and the size of `K` rounds. -/
theorem rounds_le (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    (count kinds order ballots).rounds.length ≤ max 1 (countedSet kinds).length :=
  (count_trace kinds order ballots).length_le (rule_ends order)

end Demos.Rcv.Winner
