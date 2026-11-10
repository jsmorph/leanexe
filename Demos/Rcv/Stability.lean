import Demos.Rcv.Rounds

/-!
T8 of [the requirements](requirements.md), section "Theorems", and the lemmas about the counts of
a round that T3, T10, and T11 share.  `stability_counts` and `stability_inactive` state the two
statements of T8 for `Demos.Rcv.Spec.interpret`, and `stability_rounds` its consequence for
consecutive rounds of the count.  `Closed` states that an interpretation counts a ballot only for a
member of the continuing set, and `Stable` states both statements of T8 for an interpretation: the
premises under which T10 holds for every interpretation, and from which `tally_follows` and
`majority_subset` derive the inequalities between the counts of a set and of a subset.
-/

namespace Demos.Rcv.Stability

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds

abbrev Interp := List Nat → List UInt64 → Outcome

/-- The interpretation counts a ballot, against each set `S`, only for a member of `S`. -/
def Closed (interp : Interp) : Prop :=
  ∀ (S : List Nat) (ps : List UInt64) (w : Nat), interp S ps = .counts w → w ∈ S

/-- Both statements of T8: for sets `S' ⊆ S`, a ballot that counts for `w` against `S` counts for
`w` against `S'` whenever `w ∈ S'`, and a ballot inactive against `S` with a reason is inactive
against `S'` with the same reason. -/
def Stable (interp : Interp) : Prop :=
  (∀ (S S' : List Nat) (ps : List UInt64) (w : Nat), S' ⊆ S → interp S ps = .counts w → w ∈ S' →
      interp S' ps = .counts w) ∧
    ∀ (S S' : List Nat) (ps : List UInt64) (r : Reason), S' ⊆ S → interp S ps = .inactive r →
      interp S' ps = .inactive r

/-! ## T8 for the interpretation of the requirements -/

theorem examine_counts_subset {S S' : List Nat} (hS : S' ⊆ S) {w : Nat} (hw : w ∈ S') :
    ∀ {ps : List UInt64}, examine S ps = some (.counts w) → examine S' ps = some (.counts w)
  | [], h => by simp [examine] at h
  | p :: ps, h => by
    cases hp : position p with
    | empty =>
      simp only [examine, hp] at h ⊢
      exact examine_counts_subset hS hw h
    | multiple => simp [examine, hp] at h
    | single i =>
      simp only [examine, hp] at h ⊢
      by_cases hi : i ∈ S
      · rw [ite_eq_left hi] at h
        injection h with h
        injection h with h
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

theorem interpret_closed (kinds : List Kind) : Closed (interpret kinds) :=
  fun _ _ _ h => interpret_counts h

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

/-! ## Counts of a round -/

/-- The votes of `w` against the set `S`: the number of ballots that count for `w`. -/
def votesFor (interp : Interp) (S : List Nat) (ballots : List (List UInt64)) (w : Nat) : Nat :=
  (ballots.map (interp S)).count (.counts w)

/-- Whether an outcome counts for a member of `L`. -/
def countsIn (L : List Nat) : Outcome → Bool
  | .counts i => decide (i ∈ L)
  | .inactive _ => false

theorem votes_eq (interp : Interp) (S : List Nat) (ballots : List (List UInt64)) :
    (tally interp S ballots).votes = S.map fun i : Nat => (i, votesFor interp S ballots i) := rfl

theorem mem_votes {interp : Interp} {S : List Nat} {ballots : List (List UInt64)} {i v : Nat} :
    (i, v) ∈ (tally interp S ballots).votes ↔ i ∈ S ∧ v = votesFor interp S ballots i := by
  rw [votes_eq, List.mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨ha, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem continuing_eq_sum (interp : Interp) (S : List Nat) (ballots : List (List UInt64)) :
    (tally interp S ballots).continuing = (S.map (votesFor interp S ballots)).sum := by
  unfold Tally.continuing
  rw [votes_eq, List.map_map]
  rfl

theorem countP_or_of_disjoint {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, ¬(p x = true ∧ q x = true)) →
      l.countP (fun x : α => p x || q x) = l.countP p + l.countP q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      countP_or_of_disjoint p q l fun x hx => h x (List.mem_cons_of_mem a hx)]
    have ha := h a (by simp)
    by_cases hp : p a = true <;> by_cases hq : q a = true <;> simp [hp, hq] at ha ⊢ <;> omega

/-- The votes of the members of a set without duplicates sum to the number of ballots that count
for a member of the set. -/
theorem sum_count_eq_countP (os : List Outcome) :
    ∀ {L : List Nat}, L.Nodup →
      (L.map fun i : Nat => os.count (.counts i)).sum = os.countP (countsIn L)
  | [], _ => by
    rw [List.map_nil, List.sum_nil, eq_comm, List.countP_eq_zero]
    intro o _
    cases o <;> simp [countsIn]
  | a :: L, h => by
    have ha : a ∉ L := (List.nodup_cons.mp h).1
    rw [List.map_cons, List.sum_cons, sum_count_eq_countP os (List.nodup_cons.mp h).2]
    have : countsIn (a :: L) = fun o : Outcome => (o == .counts a) || countsIn L o := by
      funext o
      cases o with
      | counts i => by_cases hi : i = a <;> simp [countsIn, hi]
      | inactive r => simp [countsIn]
    rw [this, countP_or_of_disjoint]
    · rfl
    · intro o _ ⟨h1, h2⟩
      have h1 : o = .counts a := by simpa using h1
      subst h1
      simp [countsIn, ha] at h2

theorem continuing_eq_countP (interp : Interp) {S : List Nat} (ballots : List (List UInt64))
    (hS : S.Nodup) :
    (tally interp S ballots).continuing = (ballots.map (interp S)).countP (countsIn S) := by
  rw [continuing_eq_sum]
  exact sum_count_eq_countP _ hS

theorem votesFor_le_countP (interp : Interp) (S : List Nat) (ballots : List (List UInt64))
    {L : List Nat} {w : Nat} (hw : w ∈ L) :
    votesFor interp S ballots w ≤ (ballots.map (interp S)).countP (countsIn L) := by
  unfold votesFor List.count
  apply List.countP_mono_left
  intro o _ h
  have h : o = .counts w := by simpa using h
  subst h
  simp [countsIn, hw]

/-- The votes of two members of a set without duplicates sum to at most `T`. -/
theorem two_le_continuing (interp : Interp) {S : List Nat} (ballots : List (List UInt64))
    (hS : S.Nodup) {a b : Nat} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    votesFor interp S ballots a + votesFor interp S ballots b ≤
      (tally interp S ballots).continuing := by
  rw [continuing_eq_countP interp ballots hS]
  unfold votesFor List.count
  rw [← countP_or_of_disjoint]
  · apply List.countP_mono_left
    intro o _ h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h <;> subst h <;> simp [countsIn, ha, hb]
  · intro o _ ⟨h1, h2⟩
    simp only [beq_iff_eq] at h1 h2
    rw [h1] at h2
    injection h2 with h2
    exact hab h2

theorem votesFor_le_continuing (interp : Interp) {S : List Nat} (ballots : List (List UInt64))
    (hS : S.Nodup) {a : Nat} (ha : a ∈ S) :
    votesFor interp S ballots a ≤ (tally interp S ballots).continuing := by
  rw [continuing_eq_countP interp ballots hS]
  exact votesFor_le_countP interp S ballots ha

/-- A ballot that counts for a member of `L'` against `S' ⊆ S` counts against `S` for a member of
`L'` or for a member of `S` outside `S'`, so for a member of `L` whenever `L` holds those. -/
theorem countP_transfer {interp : Interp} (hI : Closed interp) (hS : Stable interp)
    {S S' L L' : List Nat} (hsub : S' ⊆ S) (hL : ∀ i ∈ S, i ∈ L' ∨ i ∉ S' → i ∈ L)
    (ballots : List (List UInt64)) :
    (ballots.map (interp S')).countP (countsIn L') ≤
      (ballots.map (interp S)).countP (countsIn L) := by
  rw [List.countP_map, List.countP_map]
  apply List.countP_mono_left
  intro b _ h
  simp only [Function.comp] at h ⊢
  cases h1 : interp S' b with
  | inactive r =>
    rw [h1] at h
    simp [countsIn] at h
  | counts z =>
    rw [h1] at h
    have hz : z ∈ L' := by simpa [countsIn] using h
    cases h2 : interp S b with
    | inactive r =>
      rw [hS.2 S S' b r hsub h2] at h1
      cases h1
    | counts y =>
      have hy : y ∈ S := hI S b y h2
      by_cases hyS' : y ∈ S'
      · have h3 := hS.1 S S' b y hsub h2 hyS'
        rw [h1] at h3
        injection h3 with h3
        subst h3
        simpa [countsIn] using hL z hy (Or.inl hz)
      · simpa [countsIn] using hL y hy (Or.inr hyS')

theorem votesFor_mono {interp : Interp} (hS : Stable interp) {S S' : List Nat} (hsub : S' ⊆ S)
    (ballots : List (List UInt64)) {w : Nat} (hw : w ∈ S') :
    votesFor interp S ballots w ≤ votesFor interp S' ballots w := by
  unfold votesFor List.count
  rw [List.countP_map, List.countP_map]
  apply List.countP_mono_left
  intro b _ h
  simp only [Function.comp, beq_iff_eq] at h ⊢
  exact hS.1 S S' b w hsub h hw

theorem inactive_mono {interp : Interp} (hS : Stable interp) {S S' : List Nat} (hsub : S' ⊆ S)
    (ballots : List (List UInt64)) (r : Reason) :
    (ballots.map (interp S)).count (.inactive r) ≤ (ballots.map (interp S')).count (.inactive r) := by
  unfold List.count
  rw [List.countP_map, List.countP_map]
  apply List.countP_mono_left
  intro b _ h
  simp only [Function.comp, beq_iff_eq] at h ⊢
  exact hS.2 S S' b r hsub h

theorem continuing_mono {interp : Interp} (hI : Closed interp) (hS : Stable interp)
    {S S' : List Nat} (hSn : S.Nodup) (hS'n : S'.Nodup) (hsub : S' ⊆ S)
    (ballots : List (List UInt64)) :
    (tally interp S' ballots).continuing ≤ (tally interp S ballots).continuing := by
  rw [continuing_eq_countP interp ballots hSn, continuing_eq_countP interp ballots hS'n]
  exact countP_transfer hI hS hsub (fun i hi _ => hi) ballots

/-- T8's consequence for the counts of the sets `S' ⊆ S`: no inactive count decreases, the votes
of a member of `S'` do not decrease, and `T` does not increase. -/
theorem tally_follows {interp : Interp} (hI : Closed interp) (hS : Stable interp)
    {S S' : List Nat} (hSn : S.Nodup) (hS'n : S'.Nodup) (hsub : S' ⊆ S)
    (ballots : List (List UInt64)) :
    (tally interp S ballots).blank ≤ (tally interp S' ballots).blank ∧
      (tally interp S ballots).uncounted ≤ (tally interp S' ballots).uncounted ∧
      (tally interp S ballots).overvote ≤ (tally interp S' ballots).overvote ∧
      (tally interp S ballots).exhausted ≤ (tally interp S' ballots).exhausted ∧
      (∀ i v v', (i, v) ∈ (tally interp S ballots).votes →
        (i, v') ∈ (tally interp S' ballots).votes → v ≤ v') ∧
      (tally interp S' ballots).continuing ≤ (tally interp S ballots).continuing := by
  refine ⟨inactive_mono hS hsub ballots .blank, inactive_mono hS hsub ballots .uncounted,
    inactive_mono hS hsub ballots .overvote, inactive_mono hS hsub ballots .exhausted, ?_,
    continuing_mono hI hS hSn hS'n hsub ballots⟩
  intro i v v' h h'
  rw [mem_votes] at h h'
  rw [h.2, h'.2]
  exact votesFor_mono hS hsub ballots h'.1

/-- T11(a) for every interpretation that satisfies `Closed` and `Stable`: a candidate that holds a
majority of the continuing ballots against `S` holds one against every `S'` with `w ∈ S' ⊆ S`. -/
theorem majority_subset {interp : Interp} (hI : Closed interp) (hS : Stable interp)
    {S S' : List Nat} (hSn : S.Nodup) (hS'n : S'.Nodup) (hsub : S' ⊆ S)
    (ballots : List (List UInt64)) {w : Nat} (hw : w ∈ S')
    (h : (tally interp S ballots).continuing < 2 * votesFor interp S ballots w) :
    (tally interp S' ballots).continuing < 2 * votesFor interp S' ballots w := by
  have split : ∀ (T : List Nat), T.Nodup → w ∈ T →
      (tally interp T ballots).continuing =
        votesFor interp T ballots w +
          (ballots.map (interp T)).countP (countsIn (T.filter fun i : Nat => i != w)) := by
    intro T hT hwT
    rw [continuing_eq_countP interp ballots hT]
    unfold votesFor List.count
    rw [← countP_or_of_disjoint]
    · congr 1
      funext o
      cases o with
      | counts i => by_cases hi : i = w <;> simp [countsIn, hi, hwT]
      | inactive r => simp [countsIn]
    · intro o _ ⟨h1, h2⟩
      simp only [beq_iff_eq] at h1
      subst h1
      simp [countsIn] at h2
  have e1 := split S hSn (hsub hw)
  have e2 := split S' hS'n hw
  have hv := votesFor_mono hS hsub ballots hw
  have ho : (ballots.map (interp S')).countP (countsIn (S'.filter fun i : Nat => i != w)) ≤
      (ballots.map (interp S)).countP (countsIn (S.filter fun i : Nat => i != w)) := by
    apply countP_transfer hI hS hsub
    intro i hi h'
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at h' ⊢
    rcases h' with ⟨_, h'⟩ | h'
    · exact ⟨hi, h'⟩
    · exact ⟨hi, fun hiw => h' (hiw ▸ hw)⟩
  omega

/-- At most one member of a set without duplicates holds a majority. -/
theorem majority_unique (interp : Interp) {S : List Nat} (ballots : List (List UInt64))
    (hS : S.Nodup) {a b : Nat} (ha : a ∈ S) (hb : b ∈ S)
    (hma : (tally interp S ballots).continuing < 2 * votesFor interp S ballots a)
    (hmb : (tally interp S ballots).continuing < 2 * votesFor interp S ballots b) : a = b := by
  by_cases hab : a = b
  · exact hab
  · have := two_le_continuing interp ballots hS ha hb hab
    omega

/-! ## Consecutive rounds -/

/-- T8's consequence for consecutive rounds of a trace under an interpretation that satisfies
`Closed` and `Stable`, from a set without duplicates. -/
theorem trace_follows {interp : Interp} (hI : Closed interp) (hS : Stable interp)
    {decision : Tally → Decision} {ballots : List (List UInt64)} {C : List Nat} {rds : List Round}
    {w : Option Nat} (ht : Trace interp decision ballots C rds w) (hC : C.Nodup) (r : Nat)
    (h : r + 1 < rds.length) :
    rds[r].tally.blank ≤ rds[r + 1].tally.blank ∧
      rds[r].tally.uncounted ≤ rds[r + 1].tally.uncounted ∧
      rds[r].tally.overvote ≤ rds[r + 1].tally.overvote ∧
      rds[r].tally.exhausted ≤ rds[r + 1].tally.exhausted ∧
      (∀ i v v', (i, v) ∈ rds[r].tally.votes → (i, v') ∈ rds[r + 1].tally.votes → v ≤ v') ∧
      rds[r + 1].tally.continuing ≤ rds[r].tally.continuing := by
  obtain ⟨e, -, hnext⟩ := ht.next r h
  obtain ⟨ha, hsa, -⟩ := ht.mem rds[r] (List.getElem_mem (by omega))
  obtain ⟨hb, hsb, -⟩ := ht.mem rds[r + 1] (List.getElem_mem h)
  rw [ha, hb]
  have hsub : continuingSet rds[r + 1] ⊆ continuingSet rds[r] := by
    rw [hnext]
    exact List.filter_sublist.subset
  exact tally_follows hI hS (hsa.nodup hC) (hsb.nodup hC) hsub ballots

/-- T8's consequence: from each round of the count to the next, each inactive count does not
decrease, the votes of a candidate that continues do not decrease, and `T` does not increase. -/
theorem stability_rounds (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    (r : Nat) (h : r + 1 < (count kinds order ballots).rounds.length) :
    let rds := (count kinds order ballots).rounds
    rds[r].tally.blank ≤ rds[r + 1].tally.blank ∧
      rds[r].tally.uncounted ≤ rds[r + 1].tally.uncounted ∧
      rds[r].tally.overvote ≤ rds[r + 1].tally.overvote ∧
      rds[r].tally.exhausted ≤ rds[r + 1].tally.exhausted ∧
      (∀ i v v', (i, v) ∈ rds[r].tally.votes → (i, v') ∈ rds[r + 1].tally.votes → v ≤ v') ∧
      rds[r + 1].tally.continuing ≤ rds[r].tally.continuing :=
  trace_follows (interpret_closed kinds) (interpret_stable kinds)
    (count_trace kinds order ballots) (countedSet_nodup kinds) r h

/-! ## Traces -/

section Traces

variable {interp : Interp} {decision : Tally → Decision} {ballots : List (List UInt64)}

/-- A count from a set has one trace. -/
theorem trace_unique {C : List Nat} {rds rds' : List Round} {w w' : Option Nat}
    (h : Trace interp decision ballots C rds w) (h' : Trace interp decision ballots C rds' w') :
    rds = rds' ∧ w = w' := by
  have e1 := h.run_eq (max rds.length rds'.length) (Nat.le_max_left _ _)
  have e2 := h'.run_eq (max rds.length rds'.length) (Nat.le_max_right _ _)
  rw [e1] at e2
  injection e2 with e3 e4
  exact ⟨e3, e4⟩

/-- The first round of a trace from `C` holds the counts of `C`. -/
theorem trace_cons {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace interp decision ballots C rds w) :
    ∃ e rest, rds = ⟨tally interp C ballots, e⟩ :: rest := by
  cases h with
  | last => exact ⟨none, [], rfl⟩
  | step _ _ => exact ⟨_, _, rfl⟩

theorem trace_ne_nil {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace interp decision ballots C rds w) : rds ≠ [] := by
  obtain ⟨e, rest, rfl⟩ := trace_cons h
  simp

/-- The rounds of a trace from any round on form the trace from that round's continuing set, with
the same winner. -/
theorem trace_suffix : ∀ {C : List Nat} {rds : List Round} {w : Option Nat} (p : List Round)
    {rd : Round} {q : List Round}, Trace interp decision ballots C rds w → rds = p ++ rd :: q →
      Trace interp decision ballots (continuingSet rd) (rd :: q) w
  | C, rds, w, [], rd, q, h, hr => by
    rw [List.nil_append] at hr
    subst hr
    obtain ⟨e, rest, he⟩ := trace_cons h
    have : continuingSet rd = C := by
      rw [List.cons.injEq] at he
      rw [he.1, continuingSet_tally]
    rw [this]
    exact h
  | C, rds, w, r :: p, rd, q, h, hr => by
    cases h with
    | last hd =>
      rw [List.cons_append, List.cons.injEq] at hr
      simp at hr
    | step hd ht =>
      rw [List.cons_append, List.cons.injEq] at hr
      exact trace_suffix p ht hr.2

end Traces

end Demos.Rcv.Stability
