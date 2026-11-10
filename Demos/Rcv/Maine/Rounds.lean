import Demos.Rcv.Maine.Stability

/-!
The theorems of the rounds of [the requirements](requirements.md), section "Theorems", for the
Maine count: T4 Elimination, T5 Conservation, T6 Locality, T7 Invariance, the consequence of T8 for
consecutive rounds, and T9 Order.

`decision_ends` proves `Demos.Rcv.Rounds.Ends` of `decision`, so the lemmas of
`Demos/Rcv/Rounds.lean` about `run` and `Trace` apply to the count: `count_trace` gives the trace of
its rounds from `K` when the initial test elects no one, and `count_initial` gives the count of no
rounds otherwise.  `decision_three` equates rule 2 with the Oakland module's rule 4, and
`decision_eq_eliminate`, `decision_eq_winner`, `decision_tied`, and `decision_order` describe the
decision's eliminations, its ends, its tied sets, and its use of the order.  `Eliminates` and
`Concludes` state T4's descriptions with quantifiers bounded by lists, so that the native tests of
`Demos/Rcv/Maine/Native.lean` decide the theorem's own propositions.
-/

namespace Demos.Rcv.Maine

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Stability Demos.Rcv.Variants

/-! ## Terms of the statements -/

/-- T4's description of the elimination `e` of a round with the counts `t` and the tie-break order
`order`.  Either the round has three or more candidates and the elimination is (a) a lowest
elimination of the candidate that alone has the fewest votes or (b) an elimination by order of the
member latest in the order of the two or more candidates with the fewest votes, which form the
tied set; or the round has two candidates with equal votes, which form the tied set, and the
elimination is by order of the one later in the order. -/
def Eliminates (order : List Nat) (t : Tally) (e : Elimination) : Prop :=
  (3 ≤ t.votes.length ∧
    ((∃ z ∈ fewest t.votes, fewest t.votes = [z] ∧ e = .lowest z) ∨
      (2 ≤ (fewest t.votes).length ∧ ∃ i ∈ fewest t.votes, e = .order (fewest t.votes) i ∧
        ∀ j ∈ fewest t.votes, j ∈ order ∧ order.idxOf j ≤ order.idxOf i))) ∨
  (∃ x ∈ t.votes, ∃ y ∈ t.votes, t.votes = [x, y] ∧ x.2 = y.2 ∧
    ∃ i ∈ [x.1, y.1], e = .order [x.1, y.1] i ∧
      ∀ j ∈ [x.1, y.1], j ∈ order ∧ order.idxOf j ≤ order.idxOf i)

/-- T4's description of the end of the last round, whose counts are `t`, with the winner `w`: at
most two candidates continue, and the count names no one when none continues, the candidate alone,
or the one of two with more votes. -/
def Concludes (t : Tally) (w : Option Nat) : Prop :=
  (t.votes = [] ∧ w = none) ∨ (∃ x ∈ t.votes, t.votes = [x] ∧ w = some x.1) ∨
    (∃ x ∈ t.votes, ∃ y ∈ t.votes, t.votes = [x, y] ∧
      ((y.2 < x.2 ∧ w = some x.1) ∨ (x.2 < y.2 ∧ w = some y.1)))

/-- A ballot's first position is single and marks `i`. -/
def FirstMarks (i : Nat) (ps : List UInt64) : Bool := ps.head?.map position == some (.single i)

/-! ## The decision of a round -/

theorem decision_nil {order : List Nat} {t : Tally} (h : t.votes = []) :
    decision order t = .winner none := by
  simp only [decision, h]

theorem decision_one {order : List Nat} {t : Tally} {x : Nat × Nat} (h : t.votes = [x]) :
    decision order t = .winner (some x.1) := by
  simp only [decision, h]

theorem decision_two {order : List Nat} {t : Tally} {x y : Nat × Nat} (h : t.votes = [x, y]) :
    decision order t =
      if x.2 = y.2 then .eliminate (.order [x.1, y.1] (latest order [x.1, y.1]))
      else if y.2 < x.2 then .winner (some x.1)
      else .winner (some y.1) := by
  simp only [decision, h]

/-- With three or more candidates, rule 2 decides as rule 4 of the Oakland module. -/
theorem decision_three {order : List Nat} {t : Tally} (h : 3 ≤ t.votes.length) :
    decision order t = lowestDecision order (ruleTied t.votes) := by
  unfold decision
  match hv : t.votes, h with
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | _ :: _ :: _ :: _, _ => rfl

/-- A round that eliminates has three or more candidates and rule 4's elimination, or two
candidates with equal votes and the elimination by order of the one later in the order. -/
theorem decision_eq_eliminate {order : List Nat} {t : Tally} {e : Elimination}
    (h : decision order t = .eliminate e) :
    (3 ≤ t.votes.length ∧ lowestDecision order (ruleTied t.votes) = .eliminate e) ∨
      ∃ x y, t.votes = [x, y] ∧ x.2 = y.2 ∧ e = .order [x.1, y.1] (latest order [x.1, y.1]) := by
  rcases Nat.lt_or_ge t.votes.length 3 with hl | hl
  · match hv : t.votes, hl with
    | [], _ =>
      rw [decision_nil hv] at h
      cases h
    | [x], _ =>
      rw [decision_one hv] at h
      cases h
    | [x, y], _ =>
      rw [decision_two hv] at h
      by_cases hxy : x.2 = y.2
      · rw [ite_eq_left hxy] at h
        injection h with h
        exact Or.inr ⟨x, y, rfl, hxy, h.symm⟩
      · rw [ite_eq_right hxy] at h
        split at h <;> cases h
  · exact Or.inl ⟨hl, (decision_three hl).symm.trans h⟩

/-- A round that ends the count has at most two candidates and names the one of more votes, the
one alone, or no one. -/
theorem decision_eq_winner {order : List Nat} {t : Tally} {w : Option Nat}
    (h : decision order t = .winner w) : Concludes t w := by
  rcases Nat.lt_or_ge t.votes.length 3 with hl | hl
  · unfold Concludes
    match hv : t.votes, hl with
    | [], _ =>
      rw [decision_nil hv] at h
      injection h with h
      exact Or.inl ⟨rfl, h.symm⟩
    | [x], _ =>
      rw [decision_one hv] at h
      injection h with h
      exact Or.inr (Or.inl ⟨x, by simp, rfl, h.symm⟩)
    | [x, y], _ =>
      rw [decision_two hv] at h
      by_cases hxy : x.2 = y.2
      · rw [ite_eq_left hxy] at h
        cases h
      · rw [ite_eq_right hxy] at h
        refine Or.inr (Or.inr ⟨x, by simp, y, by simp, rfl, ?_⟩)
        by_cases hyx : y.2 < x.2
        · rw [ite_eq_left hyx] at h
          injection h with h
          exact Or.inl ⟨hyx, h.symm⟩
        · rw [ite_eq_right hyx] at h
          injection h with h
          exact Or.inr ⟨by omega, h.symm⟩
  · rw [decision_three hl] at h
    unfold lowestDecision at h
    split at h <;> cases h

theorem decision_ends (order : List Nat) : Ends (decision order) := by
  refine ⟨fun t e h => ?_, fun t ht => ?_⟩
  · rcases decision_eq_eliminate h with ⟨hl, h⟩ | ⟨x, y, hv, -, rfl⟩
    · exact lowest_ends (fun hnil => by simp [hnil] at hl) h
    · refine ⟨by simp [Elimination.eliminated], fun i hi => ?_⟩
      simp only [Elimination.eliminated, List.mem_singleton] at hi
      subst hi
      have := latest_mem (order := order) (Z := [x.1, y.1]) (by simp)
      rw [hv]
      simpa using this
  · match hv : t.votes, ht with
    | [], _ => exact ⟨none, decision_nil hv⟩
    | [x], _ => exact ⟨some x.1, decision_one hv⟩

/-- An elimination by order names a nonempty tied set of the round's candidates and its member
latest in the order. -/
theorem decision_tied {order : List Nat} {t : Tally} {Z : List Nat} {i : Nat}
    (h : decision order t = .eliminate (.order Z i)) :
    Z ≠ [] ∧ (∀ j ∈ Z, j ∈ t.votes.map fun x : Nat × Nat => x.1) ∧ i = latest order Z := by
  rcases decision_eq_eliminate h with ⟨hl, h⟩ | ⟨x, y, hv, -, he⟩
  · have hne : t.votes ≠ [] := fun hnil => by simp [hnil] at hl
    rw [ruleTied_eq_fewest] at h
    by_cases hz : ∃ z, fewest t.votes = [z]
    · obtain ⟨z, hz⟩ := hz
      rw [hz] at h
      simp [lowestDecision] at h
    · rw [lowestDecision_of_ne (fun z h' => hz ⟨z, h'⟩)] at h
      injection h with h
      injection h with hZ hi
      subst hZ
      subst hi
      exact ⟨fewest_ne_nil hne, fun j hj => fewest_sub hj, rfl⟩
  · injection he with hZ hi
    subst hZ
    subst hi
    refine ⟨by simp, fun j hj => ?_, rfl⟩
    rw [hv]
    simpa using hj

/-- T4's description holds for every elimination of `decision` when the order holds each
candidate of the round once. -/
theorem decision_eliminates {order : List Nat} {t : Tally} {e : Elimination}
    (h : decision order t = .eliminate e) (hnd : order.Nodup)
    (hord : ∀ x ∈ t.votes, x.1 ∈ order) : Eliminates order t e := by
  rcases decision_eq_eliminate h with ⟨hl, h⟩ | ⟨x, y, hv, hxy, rfl⟩
  · left
    refine ⟨hl, ?_⟩
    have hne : t.votes ≠ [] := fun hnil => by simp [hnil] at hl
    have hfne := fewest_ne_nil hne
    rw [ruleTied_eq_fewest] at h
    by_cases hz : ∃ z, fewest t.votes = [z]
    · obtain ⟨z, hz⟩ := hz
      rw [hz] at h
      simp only [lowestDecision, Decision.eliminate.injEq] at h
      exact Or.inl ⟨z, by rw [hz]; simp, hz, h.symm⟩
    · have hz' : ∀ z, fewest t.votes ≠ [z] := fun z h' => hz ⟨z, h'⟩
      rw [lowestDecision_of_ne hz'] at h
      injection h with h
      subst h
      have hsub : ∀ j ∈ fewest t.votes, j ∈ order := by
        intro j hj
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (fewest_sub hj)
        exact hord x hx
      obtain ⟨hmem, hlast⟩ := latest_spec hnd hsub hfne
      refine Or.inr ⟨?_, _, hmem, rfl, hlast⟩
      match hf : fewest t.votes, hfne, hz' with
      | [], hne, _ => exact absurd rfl hne
      | [z], _, hz' => exact absurd rfl (hz' z)
      | _ :: _ :: _, _, _ => simp
  · right
    have hx : x ∈ t.votes := by rw [hv]; simp
    have hy : y ∈ t.votes := by rw [hv]; simp
    have hsub : ∀ j ∈ [x.1, y.1], j ∈ order := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hord x hx
      · exact hord y hy
    obtain ⟨hmem, hlast⟩ := latest_spec hnd hsub (by simp)
    exact ⟨x, hx, y, hy, hv, hxy, _, hmem, rfl, hlast⟩

/-- `decision` under the order `π'` decides as under `π` when, in case of an elimination by order
under `π`, `π'` chooses the same member of the tied set. -/
theorem decision_order {π π' : List Nat} {t : Tally}
    (h : ∀ Z i, decision π t = .eliminate (.order Z i) → latest π' Z = i) :
    decision π' t = decision π t := by
  rcases Nat.lt_or_ge t.votes.length 3 with hl | hl
  · match hv : t.votes, hl with
    | [], _ => rw [decision_nil hv, decision_nil hv]
    | [x], _ => rw [decision_one hv, decision_one hv]
    | [x, y], _ =>
      by_cases hxy : x.2 = y.2
      · have he := h [x.1, y.1] (latest π [x.1, y.1]) (by rw [decision_two hv, ite_eq_left hxy])
        rw [decision_two hv, decision_two hv, ite_eq_left hxy, ite_eq_left hxy, he]
      · rw [decision_two hv, decision_two hv, ite_eq_right hxy, ite_eq_right hxy]
  · rw [decision_three hl, decision_three hl]
    by_cases hz : ∃ z, ruleTied t.votes = [z]
    · obtain ⟨z, hz⟩ := hz
      rw [hz]
      rfl
    · have hz' : ∀ z, ruleTied t.votes ≠ [z] := fun z h' => hz ⟨z, h'⟩
      rw [lowestDecision_of_ne hz', lowestDecision_of_ne hz',
        h _ _ (by rw [decision_three hl, lowestDecision_of_ne hz'])]

/-! ## The count -/

section Count

variable {kinds : List Kind} {order : List Nat} {ballots : List (List UInt64)}

/-- When the initial test elects `w`, the count has no rounds and names `w`. -/
theorem count_initial {w : Nat} (h : initialWinner kinds ballots = some w) :
    count kinds order ballots = ⟨[], some w⟩ := by
  simp only [count, h]

theorem count_run (h : initialWinner kinds ballots = none) :
    count kinds order ballots =
      run (interpret kinds) (decision order) ballots ((countedSet kinds).length + 1)
        (countedSet kinds) := by
  simp only [count, h]

/-- When the initial test elects no one, the rounds of the count form a trace from `K`. -/
theorem count_trace (h : initialWinner kinds ballots = none) :
    Trace (interpret kinds) (decision order) ballots (countedSet kinds)
      (count kinds order ballots).rounds (count kinds order ballots).winner := by
  rw [count_run h]
  exact run_trace (decision_ends order) _ _ (by omega) (by omega)

theorem firstCounts_perm {ballots' : List (List UInt64)} (h : ballots'.Perm ballots) :
    firstCounts kinds ballots' = firstCounts kinds ballots := by
  simp only [firstCounts, (h.map firstPosition).count_eq]

theorem initialWinner_perm {ballots' : List (List UInt64)} (h : ballots'.Perm ballots) :
    initialWinner kinds ballots' = initialWinner kinds ballots := by
  simp only [initialWinner, firstCounts_perm h, h.length_eq]

theorem count_perm {ballots' : List (List UInt64)} (h : ballots'.Perm ballots) :
    count kinds order ballots' = count kinds order ballots := by
  cases hi : initialWinner kinds ballots with
  | some w => rw [count_initial hi, count_initial ((initialWinner_perm h).trans hi)]
  | none => rw [count_run hi, count_run ((initialWinner_perm h).trans hi), run_perm h]

/-- T8's consequence: from each round of the count to the next, each inactive count does not
decrease, the votes of a candidate that continues do not decrease, and `T` does not increase. -/
theorem stability_rounds (r : Nat) (h : r + 1 < (count kinds order ballots).rounds.length) :
    let rds := (count kinds order ballots).rounds
    rds[r].tally.blank ≤ rds[r + 1].tally.blank ∧
      rds[r].tally.uncounted ≤ rds[r + 1].tally.uncounted ∧
      rds[r].tally.overvote ≤ rds[r + 1].tally.overvote ∧
      rds[r].tally.exhausted ≤ rds[r + 1].tally.exhausted ∧
      (∀ i v v', (i, v) ∈ rds[r].tally.votes → (i, v') ∈ rds[r + 1].tally.votes → v ≤ v') ∧
      rds[r + 1].tally.continuing ≤ rds[r].tally.continuing := by
  cases hi : initialWinner kinds ballots with
  | some w =>
    have h0 := count_initial (order := order) hi
    simp [h0] at h
  | none =>
    exact trace_follows (interpret_closed kinds) (interpret_stable kinds) (count_trace hi)
      (countedSet_nodup kinds) r h

end Count

/-! ## The theorems -/

/-- T4 Elimination.  Every round that eliminates meets `Eliminates`: three or more candidates and
a lowest elimination or an elimination by order of the tied set's member latest in the order, or
two candidates with equal votes and the elimination by order of the one later in the order.  The
last round eliminates no one and meets `Concludes`: at most two candidates, and the winner is the
one of more votes, the one alone, or none when no candidate continues. -/
theorem elimination (c : Contest) (hc : c.WellFormed) :
    (∀ rd ∈ (countContest c).rounds, ∀ e : Elimination, rd.elimination = some e →
      Eliminates c.order rd.tally e) ∧
    ∀ last : Round, (countContest c).rounds.getLast? = some last →
      last.elimination = none ∧ Concludes last.tally (countContest c).winner := by
  have hperm := hc.2.2.2.2.2.2.2.1
  have hnd : c.order.Nodup := hperm.nodup_iff.2 List.nodup_range'
  cases hi : initialWinner (kindsOf c) (positionsOf c) with
  | some w =>
    have h0 : countContest c = ⟨[], some w⟩ := count_initial hi
    rw [h0]
    exact ⟨fun rd hrd => by simp at hrd, fun last hl => by simp at hl⟩
  | none =>
    have ht : Trace (interpret (kindsOf c)) (decision c.order) (positionsOf c)
        (countedSet (kindsOf c)) (countContest c).rounds (countContest c).winner :=
      count_trace hi
    refine ⟨?_, ?_⟩
    · intro rd hrd e he
      obtain ⟨-, hsub, hrule⟩ := ht.mem rd hrd
      apply decision_eliminates (hrule e he) hnd
      intro x hx
      have hxC : x.1 ∈ continuingSet rd := List.mem_map_of_mem hx
      have hb := mem_countedSet (hsub.subset hxC)
      apply hperm.mem_iff.2
      simp only [kindsOf, List.length_map] at hb
      exact List.mem_range'_1.2 ⟨hb.1, by omega⟩
    · intro last hl
      obtain ⟨last', hl', he, hw⟩ := ht.last_round
      rw [hl] at hl'
      injection hl' with hl'
      subst hl'
      exact ⟨he, decision_eq_winner hw⟩

/-- T5 Conservation.  In every round, the votes of the continuing candidates and the inactive
counts by reason sum to the number of ballots, and `continuing` is the sum of the votes. -/
theorem conservation (c : Contest) :
    ∀ rd ∈ (countContest c).rounds,
      (rd.tally.votes.map fun x : Nat × Nat => x.2).sum + rd.tally.blank + rd.tally.uncounted +
          rd.tally.overvote + rd.tally.exhausted = c.ballots.length ∧
        rd.tally.continuing = (rd.tally.votes.map fun x : Nat × Nat => x.2).sum := by
  intro rd hrd
  cases hi : initialWinner (kindsOf c) (positionsOf c) with
  | some w =>
    have h0 : countContest c = ⟨[], some w⟩ := count_initial hi
    rw [h0] at hrd
    simp at hrd
  | none =>
    have ht : Trace (interpret (kindsOf c)) (decision c.order) (positionsOf c)
        (countedSet (kindsOf c)) (countContest c).rounds (countContest c).winner :=
      count_trace hi
    obtain ⟨htally, hsub, -⟩ := ht.mem rd hrd
    refine ⟨?_, rfl⟩
    rw [htally]
    have hlen : (positionsOf c).length = c.ballots.length := by simp [positionsOf]
    have := tally_sum (interpret (kindsOf c)) (continuingSet rd) (positionsOf c)
      (hsub.nodup (countedSet_nodup _)) (fun _ _ h => interpret_counts h)
    rw [hlen] at this
    exact this

/-- T6 Locality.  When the count has rounds, round 1 has the counted set as its continuing set.  In
every round `r`, the votes of each continuing candidate `i` are the number of ballots whose
interpretation against `Cᵣ` counts for `i`, each inactive count is the number of ballots whose
interpretation against `Cᵣ` is inactive with its reason, and every round but the last eliminates,
with `Cᵣ₊₁` equal to `Cᵣ` minus the eliminated candidates.  Each `f(i)` is the number of ballots
whose first position is single and marks `i`. -/
theorem locality (c : Contest) :
    let k := countContest c
    let ballots := positionsOf c
    (∀ h : 0 < k.rounds.length, continuingSet k.rounds[0] = countedSet (kindsOf c)) ∧
    (∀ (r : Nat) (h : r < k.rounds.length),
      let C := continuingSet k.rounds[r]
      k.rounds[r].tally.votes = C.map (fun i : Nat =>
          (i, ballots.countP fun ps : List UInt64 => interpret (kindsOf c) C ps == .counts i)) ∧
        k.rounds[r].tally.blank =
          ballots.countP (fun ps : List UInt64 => interpret (kindsOf c) C ps == .inactive .blank) ∧
        k.rounds[r].tally.uncounted =
          ballots.countP (fun ps : List UInt64 =>
            interpret (kindsOf c) C ps == .inactive .uncounted) ∧
        k.rounds[r].tally.overvote =
          ballots.countP (fun ps : List UInt64 =>
            interpret (kindsOf c) C ps == .inactive .overvote) ∧
        k.rounds[r].tally.exhausted =
          ballots.countP (fun ps : List UInt64 =>
            interpret (kindsOf c) C ps == .inactive .exhausted)) ∧
    (∀ (r : Nat) (h : r + 1 < k.rounds.length), ∃ e : Elimination,
      k.rounds[r].elimination = some e ∧
        continuingSet k.rounds[r + 1] =
          (continuingSet k.rounds[r]).filter fun i : Nat => decide (i ∉ e.eliminated)) ∧
    firstContest c = (countedSet (kindsOf c)).map fun i : Nat => (i, ballots.countP (FirstMarks i))
    := by
  intro k ballots
  have hfirst : firstContest c =
      (countedSet (kindsOf c)).map fun i : Nat => (i, ballots.countP (FirstMarks i)) := by
    simp only [firstContest, firstCounts, List.count_eq_countP, List.countP_map]
    apply List.map_congr_left
    intro i _
    congr 1
    apply List.countP_congr
    intro ps _
    cases ps with
    | nil => simp [firstPosition, FirstMarks]
    | cons w ws => simp [firstPosition, FirstMarks]
  cases hi : initialWinner (kindsOf c) ballots with
  | some w =>
    have h0 : k = ⟨[], some w⟩ := count_initial hi
    refine ⟨fun h => ?_, fun r h => ?_, fun r h => ?_, hfirst⟩ <;> simp [h0] at h
  | none =>
    have ht : Trace (interpret (kindsOf c)) (decision c.order) ballots (countedSet (kindsOf c))
        k.rounds k.winner := count_trace hi
    refine ⟨fun h => ?_, ?_, ht.next, hfirst⟩
    · obtain ⟨_, h0⟩ := ht.head
      exact h0
    · intro r hr C
      obtain ⟨htally, -, -⟩ := ht.mem k.rounds[r] (List.getElem_mem hr)
      rw [htally]
      simp only [tally, List.count_eq_countP, List.countP_map, Function.comp_def]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- T7 Invariance, over contest structures.  Replacing the ballots by ballots whose position words
are a permutation of theirs, which covers a permutation of the ballots and a change of their
identifiers, added, removed, or changed, leaves the count, the first counts, and the report
unchanged. -/
theorem invariance (c : Contest) (bs : List Ballot)
    (h : (bs.map fun b : Ballot => b.positions).Perm
      (c.ballots.map fun b : Ballot => b.positions)) :
    countContest { c with ballots := bs } = countContest c ∧
      firstContest { c with ballots := bs } = firstContest c ∧
      report { c with ballots := bs } = report c := by
  have hcount : countContest { c with ballots := bs } = countContest c := count_perm h
  have hfirst : firstContest { c with ballots := bs } = firstContest c := firstCounts_perm h
  have hlen : bs.length = c.ballots.length := by
    simpa using h.length_eq
  refine ⟨hcount, hfirst, ?_⟩
  simp only [report, reportLines, hcount, hfirst, headerLines, hlen]

theorem reportLines_order (c : Contest) :
    reportLines c =
      ([ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]] ++
          [spaced [ascii "contest", c.contest], spaced [ascii "positions", decimal c.positions],
            spaced [ascii "candidates", decimal c.candidates.length]] ++
          (c.candidates.zipIdx 1).map (fun p : Candidate × Nat =>
            spaced [ascii "candidate", decimal p.2, ascii (kindWord p.1.kind), p.1.name])) ++
        spaced (ascii "order" :: c.order.map decimal) ::
          ([spaced [ascii "ballots", decimal c.ballots.length]] ++ firstLines (firstContest c) ++
            (((countContest c).rounds.zipIdx 1).flatMap fun p : Round × Nat =>
              roundLines p.2 p.1) ++
            [winnerLine (countContest c).winner]) := by
  simp [reportLines, headerLines]

/-- T9 Order.  If an order `π'`, a permutation of the candidates, chooses at each round that the
count marks as a tie the candidate that the count eliminates, that is, if that candidate is the
member of the tied set latest in `π'`, then the count under `π'` has the same rounds and the same
winner, and the report's lines differ only in the order line. -/
theorem order_choice (c : Contest) (π' : List Nat)
    (hπ : π'.Perm (List.range' 1 c.candidates.length))
    (h : ∀ rd ∈ (countContest c).rounds, ∀ (Z : List Nat) (i : Nat),
      rd.elimination = some (.order Z i) → ∀ j ∈ Z, π'.idxOf j ≤ π'.idxOf i) :
    countContest { c with order := π' } = countContest c ∧
      ∃ A B : List (List UInt8),
        reportLines c = A ++ spaced (ascii "order" :: c.order.map decimal) :: B ∧
        reportLines { c with order := π' } =
          A ++ spaced (ascii "order" :: π'.map decimal) :: B := by
  have hnd : π'.Nodup := hπ.nodup_iff.2 List.nodup_range'
  have hcount : countContest { c with order := π' } = countContest c := by
    show count (kindsOf c) π' (positionsOf c) = count (kindsOf c) c.order (positionsOf c)
    cases hi : initialWinner (kindsOf c) (positionsOf c) with
    | some w => rw [count_initial hi, count_initial hi]
    | none =>
      rw [count_run hi, count_run hi]
      have ht := run_trace (interp := interpret (kindsOf c)) (ballots := positionsOf c)
        (decision_ends c.order) ((countedSet (kindsOf c)).length + 1) (countedSet (kindsOf c))
        (by omega) (by omega)
      apply run_congr
      intro rd hrd
      apply decision_order
      intro Z i he
      obtain ⟨-, hsub, -⟩ := ht.mem rd hrd
      have hel : rd.elimination = some (.order Z i) := run_elimination _ _ rd hrd _ he
      have hrd' : rd ∈ (countContest c).rounds := by
        show rd ∈ (count (kindsOf c) c.order (positionsOf c)).rounds
        rw [count_run hi]
        exact hrd
      obtain ⟨hne, hZ, rfl⟩ := decision_tied he
      have hle := h rd hrd' Z _ hel
      have hsubπ : ∀ j ∈ Z, j ∈ π' := by
        intro j hj
        have hb := mem_countedSet (hsub.subset (hZ j hj))
        simp only [kindsOf, List.length_map] at hb
        exact hπ.mem_iff.2 (List.mem_range'_1.2 ⟨hb.1, by omega⟩)
      obtain ⟨hmem', hlast'⟩ := latest_spec hnd hsubπ hne
      have hmem : latest c.order Z ∈ Z := latest_mem hne
      have h1 := hle _ hmem'
      have h2 := (hlast' _ hmem).2
      exact idxOf_inj (hsubπ _ hmem') (hsubπ _ hmem) (by omega)
  have hfirst : firstContest { c with order := π' } = firstContest c := rfl
  refine ⟨hcount, _, _, reportLines_order c, ?_⟩
  rw [reportLines_order, hcount, hfirst]

end Demos.Rcv.Maine
