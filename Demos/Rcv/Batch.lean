import Demos.Rcv.Stability
import Demos.Rcv.Variants

/-!
T10 of [the requirements](requirements.md), section "Theorems": for every interpretation that
satisfies `Demos.Rcv.Stability.Closed` and `Demos.Rcv.Stability.Stable`, the count and the single
count name the same winner, the rounds of the count are rounds of the single count, and inside a
batch the single count eliminates one member of the batch per round.

`BatchAt` collects the facts about a round with the continuing set `C` that eliminates the batch
`B = L(X)`.  For a set `D` between `C` minus the batch and `C`, the members of the batch that
continue in `D` have fewer votes against `D` than every other member of `D` (`batch_lt`), so rule 4
eliminates one of them (`batch_fewest`), no member of the batch holds a majority against `D`
(`batch_holder`), and a candidate that does holds one against `C` minus the batch
(`batch_holder_rest`).
-/

namespace Demos.Rcv.Batch

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Stability Demos.Rcv.Variants

variable {interp : Interp} {ballots : List (List UInt64)}

/-! ## Rule 4 -/

/-- Rule 4 for the counts of a nonempty set eliminates one member with the fewest votes. -/
theorem lowest_min {order : List Nat} {S : List Nat} {e : Elimination} (hS : S ≠ [])
    (h : lowestDecision order (ruleTied (tally interp S ballots).votes) = .eliminate e) :
    ∃ z ∈ S, e.eliminated = [z] ∧
      ∀ y ∈ S, votesFor interp S ballots z ≤ votesFor interp S ballots y := by
  have hne : (tally interp S ballots).votes ≠ [] := by
    rw [votes_eq]
    simpa using hS
  obtain ⟨z, hz, he⟩ := lowest_eliminated hne h
  obtain ⟨v, hv, hmin⟩ := fewest_min hz
  obtain ⟨hzS, rfl⟩ := mem_votes.1 hv
  exact ⟨z, hzS, he, fun y hy => hmin (y, votesFor interp S ballots y) (mem_votes.2 ⟨hy, rfl⟩)⟩

/-! ## The batch of a round -/

/-- The round with the continuing set `C` eliminates the batch `B = L(X)`: `B` holds the members of
`C` with fewer votes than `X`, two or more, whose votes sum to fewer than `X`'s, and no member of
`C` holds a majority. -/
structure BatchAt (interp : Interp) (ballots : List (List UInt64)) (C B : List Nat) (X : Nat) :
    Prop where
  nodup : C.Nodup
  mem : X ∈ C
  members : B = C.filter fun i : Nat =>
    decide (votesFor interp C ballots i < votesFor interp C ballots X)
  sum_lt : (ballots.map (interp C)).countP (countsIn B) < votesFor interp C ballots X
  two_le : 2 ≤ B.length
  no_majority : ∀ i ∈ C, 2 * votesFor interp C ballots i ≤ (tally interp C ballots).continuing

theorem lower_members (C : List Nat) (v : Nat) :
    (lower (tally interp C ballots).votes v).map (fun y : Nat × Nat => y.1) =
      C.filter fun i : Nat => decide (votesFor interp C ballots i < v) := by
  simp [lower, votes_eq, List.filter_map, Function.comp_def]

theorem lower_sum (C : List Nat) (v : Nat) :
    ((lower (tally interp C ballots).votes v).map fun y : Nat × Nat => y.2).sum =
      ((C.filter fun i : Nat => decide (votesFor interp C ballots i < v)).map
        (votesFor interp C ballots)).sum := by
  simp [lower, votes_eq, List.filter_map, Function.comp_def]

/-- A round that `rule` ends with a batch eliminates `L(X)` for some `X`. -/
theorem batchAt_of_rule {order C B : List Nat} (hC : C.Nodup)
    (h : rule order (tally interp C ballots) = .eliminate (.batch B)) :
    ∃ X, BatchAt interp ballots C B X := by
  obtain ⟨-, hmaj, hcases⟩ := rule_eq_eliminate h
  rcases hcases with ⟨s, hs, he⟩ | ⟨-, ⟨z, -, he⟩ | ⟨-, he⟩⟩
  · injection he with he
    subst he
    obtain ⟨hlen, ⟨x, hx, hq, rfl⟩, -⟩ := batch_some hs
    obtain ⟨hX, hxv⟩ := mem_votes.1 (show (x.1, x.2) ∈ (tally interp C ballots).votes from hx)
    refine ⟨x.1, ⟨hC, hX, ?_, ?_, hlen, ?_⟩⟩
    · rw [lower_members, hxv]
    · unfold qualifies at hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      have hnd : (C.filter fun i : Nat => decide (votesFor interp C ballots i < x.2)).Nodup :=
        List.filter_sublist.nodup hC
      rw [lower_members, ← sum_count_eq_countP _ hnd]
      have := hq.2
      rw [lower_sum] at this
      rw [← hxv]
      exact this
    · intro i hi
      exact hmaj (i, votesFor interp C ballots i) (mem_votes.2 ⟨hi, rfl⟩)
  · cases he
  · cases he

/-- `C` minus the batch `B`, the continuing set of the round after the batch. -/
abbrev rest (C B : List Nat) : List Nat := C.filter fun i : Nat => decide (i ∉ B)

theorem rest_sub {C B D : List Nat} (hCD : ∀ i ∈ C, i ∉ D → i ∈ B) : rest C B ⊆ D := by
  intro i hi
  obtain ⟨hiC, hiB⟩ := List.mem_filter.1 hi
  by_cases h : i ∈ D
  · exact h
  · simp [hCD i hiC h] at hiB

namespace BatchAt

variable {C B : List Nat} {X : Nat} (hb : BatchAt interp ballots C B X)
include hb

theorem mem_iff {i : Nat} :
    i ∈ B ↔ i ∈ C ∧ votesFor interp C ballots i < votesFor interp C ballots X := by
  rw [hb.members, List.mem_filter, decide_eq_true_eq]

theorem not_mem_X : X ∉ B := fun h => Nat.lt_irrefl _ (hb.mem_iff.1 h).2

theorem sub {i : Nat} (h : i ∈ B) : i ∈ C := (hb.mem_iff.1 h).1

theorem batch_nodup : B.Nodup := by
  rw [hb.members]
  exact List.filter_sublist.nodup hb.nodup

/-- Under an interpretation that satisfies T8, the members of the batch that continue in a set `D`
between `C` minus the batch and `C` have fewer votes against `D` than every other member of `D`. -/
theorem batch_lt (hI : Closed interp) (hS : Stable interp) {D : List Nat} (hDC : D ⊆ C)
    (hCD : ∀ i ∈ C, i ∉ D → i ∈ B) {y x : Nat} (hy : y ∈ B) (hx : x ∈ D)
    (hxB : x ∉ B) : votesFor interp D ballots y < votesFor interp D ballots x := by
  have h1 := votesFor_le_countP interp D ballots hy
  have h2 : (ballots.map (interp D)).countP (countsIn B) ≤
      (ballots.map (interp C)).countP (countsIn B) := by
    apply countP_transfer hI hS hDC
    intro i hi h'
    rcases h' with h' | h'
    · exact h'
    · exact hCD i hi h'
  have h3 := hb.sum_lt
  have h4 : votesFor interp C ballots X ≤ votesFor interp C ballots x := by
    have := mt (fun h => hb.mem_iff.2 ⟨hDC hx, h⟩) hxB
    omega
  have h5 := votesFor_mono hS hDC ballots hx
  omega

theorem X_mem {D : List Nat} (hCD : ∀ i ∈ C, i ∉ D → i ∈ B) : X ∈ D := by
  by_cases h : X ∈ D
  · exact h
  · exact absurd (hCD X hb.mem h) hb.not_mem_X

theorem X_pos : 0 < votesFor interp C ballots X := by
  have := hb.sum_lt
  omega

/-- `T` is positive against every set between `C` minus the batch and `C`. -/
theorem continuing_pos (hS : Stable interp) {D : List Nat} (hDC : D ⊆ C) (hD : D.Nodup)
    (hCD : ∀ i ∈ C, i ∉ D → i ∈ B) : 0 < (tally interp D ballots).continuing := by
  have hX := hb.X_mem hCD
  have h1 := votesFor_mono hS hDC ballots hX
  have h2 := votesFor_le_continuing interp ballots hD hX
  have h3 := hb.X_pos
  omega

/-- No member of the batch holds a majority against a set between `C` minus the batch and `C`. -/
theorem batch_holder (hI : Closed interp) (hS : Stable interp) {D : List Nat} (hDC : D ⊆ C)
    (hD : D.Nodup) (hCD : ∀ i ∈ C, i ∉ D → i ∈ B) {w : Nat} (hwD : w ∈ D)
    (hw : (tally interp D ballots).continuing < 2 * votesFor interp D ballots w) : w ∉ B := by
  intro hwB
  have hX := hb.X_mem hCD
  have hlt := hb.batch_lt hI hS hDC hCD hwB hX hb.not_mem_X
  have hne : w ≠ X := fun h => hb.not_mem_X (h ▸ hwB)
  have := two_le_continuing interp ballots hD hwD hX hne
  omega

/-- A candidate that holds a majority against a set between `C` minus the batch and `C` holds one
against `C` minus the batch. -/
theorem batch_holder_rest (hI : Closed interp) (hS : Stable interp) {D : List Nat} (hDC : D ⊆ C)
    (hD : D.Nodup) (hCD : ∀ i ∈ C, i ∉ D → i ∈ B) {w : Nat} (hwD : w ∈ D)
    (hw : (tally interp D ballots).continuing < 2 * votesFor interp D ballots w) :
    w ∈ rest C B ∧
      (tally interp (rest C B) ballots).continuing < 2 * votesFor interp (rest C B) ballots w := by
  have hwB := hb.batch_holder hI hS hDC hD hCD hwD hw
  have hmem : w ∈ rest C B := List.mem_filter.2 ⟨hDC hwD, by simp [hwB]⟩
  exact ⟨hmem, majority_subset hI hS hD (List.filter_sublist.nodup hb.nodup) (rest_sub hCD)
    ballots hmem hw⟩

/-- Rule 4 against a set between `C` minus the batch and `C` that holds a member of the batch
eliminates one member of the batch. -/
theorem batch_fewest (hI : Closed interp) (hS : Stable interp) {order D : List Nat} {e : Elimination}
    (hDC : D ⊆ C) (hCD : ∀ i ∈ C, i ∉ D → i ∈ B) {b : Nat} (hbB : b ∈ B) (hbD : b ∈ D)
    (h : lowestDecision order (ruleTied (tally interp D ballots).votes) = .eliminate e) :
    ∃ z ∈ B, z ∈ D ∧ e.eliminated = [z] := by
  obtain ⟨z, hzD, he, hmin⟩ := lowest_min (List.ne_nil_of_mem hbD) h
  refine ⟨z, ?_, hzD, he⟩
  by_cases hzB : z ∈ B
  · exact hzB
  · have := hb.batch_lt hI hS hDC hCD hbB hzD hzB
    have := hmin b hbD
    omega

/-- `C` minus the batch has two or more members, since `X` would otherwise hold a majority. -/
theorem rest_two_le : 2 ≤ (rest C B).length := by
  have hXr : X ∈ rest C B := List.mem_filter.2 ⟨hb.mem, by simp [hb.not_mem_X]⟩
  have hother : ∃ i ∈ C, i ∉ B ∧ i ≠ X := by
    refine Classical.byContradiction fun hno' => ?_
    have hno : ∀ i ∈ C, i ∉ B → i = X := fun i hi hiB =>
      Classical.byContradiction fun hiX => hno' ⟨i, hi, hiB, hiX⟩
    have hle : (tally interp C ballots).continuing ≤
        votesFor interp C ballots X + (ballots.map (interp C)).countP (countsIn B) := by
      rw [continuing_eq_countP interp ballots hb.nodup]
      unfold votesFor List.count
      rw [← countP_or_of_disjoint]
      · apply List.countP_mono_left
        intro o _ h
        cases o with
        | inactive r => simp [countsIn] at h
        | counts i =>
          have hi : i ∈ C := by simpa [countsIn] using h
          by_cases hiB : i ∈ B
          · simp [countsIn, hiB]
          · simp [hno i hi hiB]
      · intro o _ ⟨h1, h2⟩
        simp only [beq_iff_eq] at h1
        subst h1
        simp [countsIn, hb.not_mem_X] at h2
    have := hb.no_majority X hb.mem
    have := hb.sum_lt
    omega
  obtain ⟨i, hiC, hiB, hiX⟩ := hother
  have hir : i ∈ rest C B := List.mem_filter.2 ⟨hiC, by simp [hiB]⟩
  match h : rest C B, hXr, hir with
  | [], hXr, _ => simp at hXr
  | [a], hXr, hir =>
    simp only [List.mem_singleton] at hXr hir
    exact absurd (hir.trans hXr.symm) hiX
  | _ :: _ :: _, _, _ => simp

end BatchAt

/-! ## Decisions -/

theorem lowestDecision_ne_winner {order Z : List Nat} {w : Option Nat} :
    lowestDecision order Z ≠ .winner w := by
  unfold lowestDecision
  split <;> simp

theorem ruleSingle_lowest {order : List Nat} {t : Tally} {e : Elimination}
    (h : ruleSingle order t = .eliminate e) :
    lowestDecision order (ruleTied t.votes) = .eliminate e := by
  unfold ruleSingle at h
  split at h
  · cases h
  · by_cases h0 : t.continuing = 0
    · rw [ite_eq_left h0] at h
      cases h
    · rw [ite_eq_right h0] at h
      exact h

theorem ruleCounty_lowest {order : List Nat} {t : Tally} {e : Elimination}
    (h : ruleCounty order t = .eliminate e) :
    lowestDecision order (ruleTied t.votes) = .eliminate e := by
  unfold ruleCounty at h
  by_cases h2 : t.votes.length ≤ 2
  · rw [ite_eq_left h2] at h
    cases h
  · rw [ite_eq_right h2] at h
    exact h

theorem ruleSingle_winner {order : List Nat} {t : Tally} {w : Option Nat}
    (h : ruleSingle order t = .winner w) :
    (∃ x ∈ t.votes, t.continuing < 2 * x.2 ∧ w = some x.1) ∨ (t.continuing = 0 ∧ w = none) := by
  unfold ruleSingle at h
  split at h
  · rename_i x hx
    injection h with h
    exact Or.inl ⟨x, List.mem_of_find?_eq_some hx, by simpa using List.find?_some hx, h.symm⟩
  · by_cases h0 : t.continuing = 0
    · rw [ite_eq_left h0] at h
      injection h with h
      exact Or.inr ⟨h0, h.symm⟩
    · rw [ite_eq_right h0] at h
      exact absurd h lowestDecision_ne_winner

/-- The single count decides as the count in every round that does not eliminate a batch. -/
theorem ruleSingle_eq {order : List Nat} {t : Tally}
    (h : ∀ s, rule order t ≠ .eliminate (.batch s)) : ruleSingle order t = rule order t := by
  cases hx : t.votes.find? (fun x : Nat × Nat => t.continuing < 2 * x.2) with
  | some x =>
    rw [rule_of_majority hx]
    unfold ruleSingle
    rw [hx]
  | none =>
    by_cases h0 : t.continuing = 0
    · rw [rule_of_zero hx h0]
      unfold ruleSingle
      rw [hx]
      simp only [h0, ↓reduceIte]
    · cases hb : batch t.votes with
      | some s => exact absurd (rule_of_batch hx h0 hb) (h s)
      | none =>
        rw [rule_of_lowest hx h0 hb]
        unfold ruleSingle
        rw [hx]
        simp only [h0, ↓reduceIte]

/-- When `w` holds a majority against `S`, rule 1 finds it. -/
theorem find_holder {S : List Nat} (hS : S.Nodup) {w : Nat} (hw : w ∈ S)
    (hm : (tally interp S ballots).continuing < 2 * votesFor interp S ballots w) :
    (tally interp S ballots).votes.find?
        (fun x : Nat × Nat => (tally interp S ballots).continuing < 2 * x.2) =
      some (w, votesFor interp S ballots w) := by
  cases hx : (tally interp S ballots).votes.find?
      (fun x : Nat × Nat => (tally interp S ballots).continuing < 2 * x.2) with
  | none =>
    have := List.find?_eq_none.1 hx (w, votesFor interp S ballots w) (mem_votes.2 ⟨hw, rfl⟩)
    simp [hm] at this
  | some x =>
    obtain ⟨a, v⟩ := x
    obtain ⟨haS, rfl⟩ := mem_votes.1 (List.mem_of_find?_eq_some hx)
    have hp : (tally interp S ballots).continuing < 2 * votesFor interp S ballots a := by
      simpa using List.find?_some hx
    rw [majority_unique interp ballots hS haS hw hp hm]

theorem rule_holder {order S : List Nat} (hS : S.Nodup) {w : Nat} (hw : w ∈ S)
    (hm : (tally interp S ballots).continuing < 2 * votesFor interp S ballots w) :
    rule order (tally interp S ballots) = .winner (some w) := by
  rw [rule_of_majority (find_holder hS hw hm)]

/-! ## The single count through a batch -/

/-- A round that eliminates exactly one member of `B`, a member of its continuing set. -/
def EliminatesOne (B : List Nat) (rd : Round) : Prop :=
  ∃ b ∈ B, b ∈ continuingSet rd ∧ ∃ e, rd.elimination = some e ∧ e.eliminated = [b]

theorem filter_not_mem_nil (C : List Nat) :
    (C.filter fun i : Nat => decide (i ∉ ([] : List Nat))) = C :=
  List.filter_eq_self.2 fun _ _ => by simp

theorem filter_not_mem_cons (C E : List Nat) (z : Nat) :
    (C.filter fun i : Nat => decide (i ∉ E)).filter (fun i : Nat => decide (i ∉ [z])) =
      C.filter fun i : Nat => decide (i ∉ z :: E) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases h1 : x = z <;> by_cases h2 : x ∈ E <;> simp [h1, h2]

/-- The rounds from a set between `C` minus the batch `B` and `C`, under a decision whose
eliminations are those of rule 4, such as the single count's or the county count's: either they
eliminate the members of the batch that continue, one per round, and go on with the rounds from `C`
minus the batch, or the decision ends the count against a set that still holds a member of the
batch, after rounds that each eliminate one member of the batch. -/
theorem walk {C B : List Nat} {X : Nat} (hb : BatchAt interp ballots C B X) (hI : Closed interp)
    (hS : Stable interp) {order : List Nat} {d : Tally → Decision}
    (hd : ∀ t e, d t = .eliminate e → lowestDecision order (ruleTied t.votes) = .eliminate e) :
    ∀ (n : Nat) (E : List Nat), (B.filter fun i : Nat => decide (i ∉ E)).length = n → E ⊆ B →
      ∀ {rds : List Round} {w : Option Nat},
        Trace interp d ballots (C.filter fun i : Nat => decide (i ∉ E)) rds w →
        (∃ p rds', rds = p ++ rds' ∧ Trace interp d ballots (rest C B) rds' w ∧ p.length = n ∧
            ∀ rd ∈ p, EliminatesOne B rd) ∨
          ∃ E', E' ⊆ B ∧ (∃ b ∈ B, b ∉ E') ∧
            d (tally interp (C.filter fun i : Nat => decide (i ∉ E')) ballots) = .winner w ∧
            (∀ rd ∈ rds, rd.elimination = none ∨ EliminatesOne B rd) ∧
            ∃ last, rds.getLast? = some last ∧
              continuingSet last = C.filter fun i : Nat => decide (i ∉ E')
  | 0, E, hn, hE, rds, w, ht => by
    left
    have hall : ∀ b ∈ B, b ∈ E := by
      intro b hbB
      by_cases hbE : b ∈ E
      · exact hbE
      · have hmem : b ∈ B.filter fun i : Nat => decide (i ∉ E) :=
          List.mem_filter.2 ⟨hbB, by simp [hbE]⟩
        rw [List.length_eq_zero_iff.1 hn] at hmem
        simp at hmem
    have hset : (C.filter fun i : Nat => decide (i ∉ E)) = rest C B := by
      apply List.filter_congr
      intro i _
      by_cases hiE : i ∈ E
      · simp [hiE, hE hiE]
      · have hiB : i ∉ B := fun h => hiE (hall i h)
        simp [hiE, hiB]
    rw [hset] at ht
    exact ⟨[], rds, rfl, ht, rfl, by simp⟩
  | n + 1, E, hn, hE, rds, w, ht => by
    obtain ⟨b, hb'⟩ := List.exists_mem_of_length_pos
      (show 0 < (B.filter fun i : Nat => decide (i ∉ E)).length by omega)
    obtain ⟨hbB, hbE⟩ := List.mem_filter.1 hb'
    simp only [decide_eq_true_eq] at hbE
    have hDC : (C.filter fun i : Nat => decide (i ∉ E)) ⊆ C := List.filter_sublist.subset
    have hCD : ∀ i ∈ C, i ∉ (C.filter fun i : Nat => decide (i ∉ E)) → i ∈ B := by
      intro i hi h
      by_cases hiE : i ∈ E
      · exact hE hiE
      · exact absurd (List.mem_filter.2 ⟨hi, by simp [hiE]⟩) h
    have hbD : b ∈ C.filter fun i : Nat => decide (i ∉ E) :=
      List.mem_filter.2 ⟨hb.sub hbB, by simp [hbE]⟩
    cases ht with
    | last hw =>
      right
      exact ⟨E, hE, ⟨b, hbB, hbE⟩, hw, by simp, _, rfl, continuingSet_tally _ _ _ _⟩
    | step he hrest =>
      rename_i e rds'
      obtain ⟨z, hzB, hzD, hez⟩ := hb.batch_fewest hI hS hDC hCD hbB hbD (hd _ _ he)
      rw [hez, filter_not_mem_cons] at hrest
      have hzE : z ∉ E := by simpa using (List.mem_filter.1 hzD).2
      have hn' : (B.filter fun i : Nat => decide (i ∉ z :: E)).length = n := by
        have hL : (B.filter fun i : Nat => decide (i ∉ E)).Nodup :=
          List.filter_sublist.nodup hb.batch_nodup
        have hzL : z ∈ B.filter fun i : Nat => decide (i ∉ E) :=
          List.mem_filter.2 ⟨hzB, by simp [hzE]⟩
        have heq : (B.filter fun i : Nat => decide (i ∉ z :: E)) =
            (B.filter fun i : Nat => decide (i ∉ E)).erase z := by
          rw [hL.erase_eq_filter, List.filter_filter]
          apply List.filter_congr
          intro x _
          by_cases h1 : x = z <;> by_cases h2 : x ∈ E <;> simp [h1, h2]
        rw [heq, List.length_erase_of_mem hzL, hn]
        rfl
      have hE' : z :: E ⊆ B := by
        intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · exact hzB
        · exact hE hi
      have hround : EliminatesOne B
          ⟨tally interp (C.filter fun i : Nat => decide (i ∉ E)) ballots, some e⟩ :=
        ⟨z, hzB, by rw [continuingSet_tally]; exact hzD, e, rfl, hez⟩
      rcases walk hb hI hS hd n (z :: E) hn' hE' hrest with
        ⟨p, rds'', h1, h2, h3, h4⟩ | ⟨E', h1, h2, h3, h4, last, h5, h6⟩
      · left
        refine ⟨_ :: p, rds'', by rw [h1]; rfl, h2, by simp [h3], ?_⟩
        intro rd hrd
        rcases List.mem_cons.1 hrd with rfl | hrd
        · exact hround
        · exact h4 rd hrd
      · right
        refine ⟨E', h1, h2, h3, ?_, last, ?_, h6⟩
        · intro rd hrd
          rcases List.mem_cons.1 hrd with rfl | hrd
          · exact Or.inr hround
          · exact h4 rd hrd
        · rw [List.getLast?_cons, h5]
          rfl

/-! ## T10 -/

/-- T10 over traces: the count and the single count from a set without duplicates name the same
winner, and the rounds of the count are rounds of the single count, but for the last when the
single count ends at a continuing set that strictly contains the count's last one. -/
theorem batch_trace (hI : Closed interp) (hS : Stable interp) {order : List Nat} :
    ∀ {C : List Nat} {rds : List Round} {w : Option Nat},
      Trace interp (rule order) ballots C rds w → C.Nodup →
      ∀ {srds : List Round} {sw : Option Nat}, Trace interp (ruleSingle order) ballots C srds sw →
        sw = w ∧ ((rds.map Round.tally).Sublist (srds.map Round.tally) ∨
          ((rds.map Round.tally).dropLast.Sublist (srds.map Round.tally) ∧ sw = w ∧
            ∃ a b, rds.getLast? = some a ∧ srds.getLast? = some b ∧
              continuingSet a ⊆ continuingSet b ∧ ∃ x ∈ continuingSet b, x ∉ continuingSet a)) := by
  intro C rds w ht
  induction ht with
  | @last C w hr =>
    intro _ srds sw hs
    have hsr : ruleSingle order (tally interp C ballots) = .winner w := by
      rw [ruleSingle_eq (fun s h => by rw [hr] at h; cases h), hr]
    obtain ⟨rfl, rfl⟩ := trace_unique hs (Trace.last hsr)
    exact ⟨rfl, Or.inl (List.Sublist.refl _)⟩
  | @step C e rds w hr hrest ih =>
    intro hC srds sw hs
    have hC1 : (C.filter fun i : Nat => decide (i ∉ e.eliminated)).Nodup :=
      List.filter_sublist.nodup hC
    obtain ⟨e0, srest, hsh⟩ := trace_cons hs
    have hrne : rds ≠ [] := trace_ne_nil hrest
    by_cases hbat : ∃ B, e = .batch B
    · obtain ⟨B, rfl⟩ := hbat
      obtain ⟨X, hb⟩ := batchAt_of_rule hC hr
      have hs' : Trace interp (ruleSingle order) ballots
          (C.filter fun i : Nat => decide (i ∉ ([] : List Nat))) srds sw := by
        rw [filter_not_mem_nil]
        exact hs
      have hlen : (B.filter fun i : Nat => decide (i ∉ ([] : List Nat))).length = B.length := by
        rw [filter_not_mem_nil]
      rcases walk hb hI hS (fun _ _ h => ruleSingle_lowest h) B.length [] hlen (by simp) hs' with
        ⟨p, srds', h1, h2, h3, h4⟩ | ⟨E', hE', ⟨b, hbB, hbE'⟩, hw, -, last, hl, hls⟩
      · obtain ⟨hw', hsub⟩ := ih hC1 h2
        refine ⟨hw', ?_⟩
        obtain ⟨r0, p', rfl⟩ : ∃ r0 p', p = r0 :: p' := by
          match p, h3 with
          | r0 :: p', _ => exact ⟨r0, p', rfl⟩
          | [], h3 => have := hb.two_le; simp at h3; omega
        have hr0 : r0.tally = tally interp C ballots := by
          rw [hsh, List.cons_append, List.cons.injEq] at h1
          rw [← h1.1]
        have hsm : srds.map Round.tally =
            tally interp C ballots :: (p'.map Round.tally ++ srds'.map Round.tally) := by
          rw [h1]
          simp [hr0]
        have hne' : srds' ≠ [] := trace_ne_nil h2
        rcases hsub with hsub | ⟨hsub, -, a, b', ha, hb', hab, x, hx, hxa⟩
        · left
          rw [List.map_cons, hsm]
          exact (hsub.trans (List.sublist_append_right _ _)).cons_cons _
        · right
          refine ⟨?_, hw', a, b', ?_, ?_, hab, x, hx, hxa⟩
          · rw [List.map_cons, List.dropLast_cons_of_ne_nil (by simpa using hrne), hsm]
            exact (hsub.trans (List.sublist_append_right _ _)).cons_cons _
          · rw [List.getLast?_cons, ha]
            rfl
          · rw [h1, List.getLast?_append, hb']
            rfl
      · have hD' : (C.filter fun i : Nat => decide (i ∉ E')).Nodup := List.filter_sublist.nodup hC
        have hDC : (C.filter fun i : Nat => decide (i ∉ E')) ⊆ C := List.filter_sublist.subset
        have hCD : ∀ i ∈ C, i ∉ (C.filter fun i : Nat => decide (i ∉ E')) → i ∈ B := by
          intro i hi h
          by_cases hiE : i ∈ E'
          · exact hE' hiE
          · exact absurd (List.mem_filter.2 ⟨hi, by simp [hiE]⟩) h
        have hbD : b ∈ C.filter fun i : Nat => decide (i ∉ E') :=
          List.mem_filter.2 ⟨hb.sub hbB, by simp [hbE']⟩
        rcases ruleSingle_winner hw with ⟨⟨w', v⟩, hxv, hmaj, rfl⟩ | ⟨h0, -⟩
        · obtain ⟨hw'D, rfl⟩ := mem_votes.1 hxv
          obtain ⟨hw'r, hmr⟩ := hb.batch_holder_rest hI hS hDC hD' hCD hw'D hmaj
          have hrule := rule_holder (order := order) (List.filter_sublist.nodup hC) hw'r hmr
          obtain ⟨rfl, rfl⟩ := trace_unique hrest (Trace.last hrule)
          refine ⟨rfl, Or.inr ⟨?_, rfl,
            ⟨tally interp (C.filter fun i : Nat => decide (i ∉ B)) ballots, none⟩, last, rfl, hl,
            ?_, b, ?_, ?_⟩⟩
          · rw [hsh]
            simp
          · rw [continuingSet_tally, hls]
            exact rest_sub hCD
          · rw [hls]
            exact hbD
          · rw [continuingSet_tally]
            intro h
            simp [hbB] at h
        · have := hb.continuing_pos hS hDC hD' hCD
          omega
    · have hnb : ∀ s, rule order (tally interp C ballots) ≠ .eliminate (.batch s) := by
        intro s h
        rw [hr] at h
        injection h with h
        exact hbat ⟨s, h⟩
      have hsr := ruleSingle_eq hnb
      rw [hr] at hsr
      cases hs with
      | last h' =>
        rw [hsr] at h'
        cases h'
      | step h' hsrest =>
        rename_i e' srest'
        rw [hsr] at h'
        injection h' with h'
        subst h'
        obtain ⟨hw', hsub⟩ := ih hC1 hsrest
        refine ⟨hw', ?_⟩
        have hsne : srest' ≠ [] := trace_ne_nil hsrest
        rcases hsub with hsub | ⟨hsub, -, a, b', ha, hb', hab, x, hx, hxa⟩
        · exact Or.inl (hsub.cons_cons _)
        · right
          refine ⟨?_, hw', a, b', ?_, ?_, hab, x, hx, hxa⟩
          · rw [List.map_cons, List.dropLast_cons_of_ne_nil (by simpa using hrne), List.map_cons]
            exact hsub.cons_cons _
          · rw [List.getLast?_cons, ha]
            rfl
          · rw [List.getLast?_cons, hb']
            rfl

/-- T10(a) for every interpretation that satisfies T8 and counts a ballot only for a member of the
continuing set: from a set without duplicates, the count and the single count name the same
winner, or both none. -/
theorem run_batch_winner (hI : Closed interp) (hS : Stable interp) (order : List Nat)
    (ballots : List (List UInt64)) {C : List Nat} (hC : C.Nodup) :
    (run interp (ruleSingle order) ballots (C.length + 1) C).winner =
      (run interp (rule order) ballots (C.length + 1) C).winner :=
  (batch_trace hI hS (run_trace (rule_ends order) _ _ (by omega) (by omega)) hC
    (run_trace (ruleSingle_ends order) _ _ (by omega) (by omega))).1

/-- T10(b) for every interpretation that satisfies T8 and counts a ballot only for a member of the
continuing set: each round of the count is a round of the single count, with the same counts, in
the same order, unless the single count ends earlier: then every round of the count but the last
is a round of the single count, the single count names the count's winner, and its last continuing
set strictly contains the count's last one. -/
theorem run_batch_rounds (hI : Closed interp) (hS : Stable interp) (order : List Nat)
    (ballots : List (List UInt64)) {C : List Nat} (hC : C.Nodup) :
    let k := run interp (rule order) ballots (C.length + 1) C
    let k' := run interp (ruleSingle order) ballots (C.length + 1) C
    (k.rounds.map Round.tally).Sublist (k'.rounds.map Round.tally) ∨
      ((k.rounds.map Round.tally).dropLast.Sublist (k'.rounds.map Round.tally) ∧
        k'.winner = k.winner ∧
        ∃ a b, k.rounds.getLast? = some a ∧ k'.rounds.getLast? = some b ∧
          continuingSet a ⊆ continuingSet b ∧ ∃ x ∈ continuingSet b, x ∉ continuingSet a) :=
  (batch_trace hI hS (run_trace (rule_ends order) _ _ (by omega) (by omega)) hC
    (run_trace (ruleSingle_ends order) _ _ (by omega) (by omega))).2

/-- T10(c) for every interpretation that satisfies T8 and counts a ballot only for a member of the
continuing set: once the single count reaches the continuing set of a round of the count that
eliminates the batch `B`, each of its rounds, for as many rounds as `B` has members, eliminates one
member of `B` that continues in it and no other candidate, or ends the single count. -/
theorem run_batch_members (hI : Closed interp) (hS : Stable interp) (order : List Nat)
    (ballots : List (List UInt64)) {C : List Nat} (hC : C.Nodup) {p q p' q' : List Round}
    {rd sd : Round} {B : List Nat}
    (hk : (run interp (rule order) ballots (C.length + 1) C).rounds = p ++ rd :: q)
    (hrd : rd.elimination = some (.batch B))
    (hk' : (run interp (ruleSingle order) ballots (C.length + 1) C).rounds = p' ++ sd :: q')
    (hset : continuingSet sd = continuingSet rd) :
    ∀ sj ∈ (sd :: q').take B.length, sj.elimination = none ∨
      ∃ b ∈ B, b ∈ continuingSet sj ∧ ∃ e, sj.elimination = some e ∧ e.eliminated = [b] := by
  have ht := run_trace (interp := interp) (ballots := ballots) (rule_ends order) (C.length + 1) C
    (by omega) (by omega)
  have hs := run_trace (interp := interp) (ballots := ballots) (ruleSingle_ends order)
    (C.length + 1) C (by omega) (by omega)
  have hsuf := trace_suffix p ht hk
  have hsuf' := trace_suffix p' hs hk'
  obtain ⟨htally, hsubC, hrule⟩ := ht.mem rd (by rw [hk]; simp)
  have hS0 : (continuingSet rd).Nodup := hsubC.nodup hC
  have hr : rule order (tally interp (continuingSet rd) ballots) = .eliminate (.batch B) := by
    rw [← htally]
    exact hrule _ hrd
  obtain ⟨X, hb⟩ := batchAt_of_rule hS0 hr
  rw [hset, ← filter_not_mem_nil (continuingSet rd)] at hsuf'
  have hlen : (B.filter fun i : Nat => decide (i ∉ ([] : List Nat))).length = B.length := by
    rw [filter_not_mem_nil]
  intro sj hsj
  rcases walk hb hI hS (fun _ _ h => ruleSingle_lowest h) B.length [] hlen (by simp) hsuf' with
    ⟨p0, rds', h1, -, h3, h4⟩ | ⟨-, -, -, -, h4, -⟩
  · rw [h1, List.take_left' h3] at hsj
    exact Or.inr (h4 sj hsj)
  · exact h4 sj (List.mem_of_mem_take hsj)

/-- T10(a) for the count of the requirements: the count and the single count name the same winner,
or both none. -/
theorem batch_winner (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    (singleCount kinds order ballots).winner = (count kinds order ballots).winner :=
  run_batch_winner (interpret_closed kinds) (interpret_stable kinds) order ballots
    (countedSet_nodup kinds)

/-- T10(b) for the count of the requirements. -/
theorem batch_rounds (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    let k := count kinds order ballots
    let k' := singleCount kinds order ballots
    (k.rounds.map Round.tally).Sublist (k'.rounds.map Round.tally) ∨
      ((k.rounds.map Round.tally).dropLast.Sublist (k'.rounds.map Round.tally) ∧
        k'.winner = k.winner ∧
        ∃ a b, k.rounds.getLast? = some a ∧ k'.rounds.getLast? = some b ∧
          continuingSet a ⊆ continuingSet b ∧ ∃ x ∈ continuingSet b, x ∉ continuingSet a) :=
  run_batch_rounds (interpret_closed kinds) (interpret_stable kinds) order ballots
    (countedSet_nodup kinds)

/-- T10(c) for the count of the requirements. -/
theorem batch_members (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {p q p' q' : List Round} {rd sd : Round} {B : List Nat}
    (hk : (count kinds order ballots).rounds = p ++ rd :: q)
    (hrd : rd.elimination = some (.batch B))
    (hk' : (singleCount kinds order ballots).rounds = p' ++ sd :: q')
    (hset : continuingSet sd = continuingSet rd) :
    ∀ sj ∈ (sd :: q').take B.length, sj.elimination = none ∨
      ∃ b ∈ B, b ∈ continuingSet sj ∧ ∃ e, sj.elimination = some e ∧ e.eliminated = [b] :=
  run_batch_members (interpret_closed kinds) (interpret_stable kinds) order ballots
    (countedSet_nodup kinds) hk hrd hk' hset

end Demos.Rcv.Batch
