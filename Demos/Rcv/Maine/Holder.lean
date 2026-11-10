import Demos.Rcv.Maine.Winner

/-!
T11 of [the requirements](requirements.md), section "Theorems", for the Maine count, which relates
the count to the count without the initial test and to the single count of
`Demos/Rcv/Maine/Variants.lean`.  (a) is `Demos.Rcv.Stability.majority_subset` for the Maine
interpretation.  `holder_trace` shows that a candidate that holds a majority in a round continues to
the end of the rounds and is named: no last place holds a majority, and two candidates of which one
holds a majority do not tie.  The initial test's winner holds a majority of round 1 of the count
without the initial test, since every ballot that ranks it first alone counts for it against `K`
(`firstCount_le_votes`).  The single count and the count without the initial test eliminate the
same candidates while the single count runs, since a round of the single count that eliminates has
no majority and a continuing ballot, so that it has two tied candidates or three or more
(`single_rounds`).
-/

namespace Demos.Rcv.Maine

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Stability Demos.Rcv.Variants
  Demos.Rcv.Batch

variable {kinds : List Kind} {order : List Nat} {ballots : List (List UInt64)}

/-! ## A majority holder -/

/-- In a trace of `decision` from a set without duplicates against which `w` holds a majority, `w`
continues in every round, and the trace names it. -/
theorem holder_trace :
    ∀ {S : List Nat} {rds : List Round} {w0 : Option Nat},
      Trace (interpret kinds) (decision order) ballots S rds w0 → S.Nodup → ∀ {w : Nat}, w ∈ S →
        (tally (interpret kinds) S ballots).continuing <
          2 * votesFor (interpret kinds) S ballots w →
        (∀ rd ∈ rds, w ∈ continuingSet rd) ∧ w0 = some w := by
  intro S rds w0 ht
  induction ht with
  | @last S w0 hr =>
    intro hSn w hw hm
    refine ⟨by simp [continuingSet_tally, hw], ?_⟩
    rw [continuing_eq_sum] at hm
    have hv := votes_eq (interpret kinds) S ballots
    rcases S with _ | ⟨a, _ | ⟨b, _ | ⟨c, S⟩⟩⟩
    · simp at hw
    · rw [decision_one (x := (a, votesFor (interpret kinds) [a] ballots a)) (by rw [hv]; rfl)]
        at hr
      injection hr with hr
      simp only [List.mem_singleton] at hw
      rw [← hr, hw]
    · rw [decision_two (x := (a, votesFor (interpret kinds) [a, b] ballots a))
        (y := (b, votesFor (interpret kinds) [a, b] ballots b)) (by rw [hv]; rfl)] at hr
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      split at hr
      · cases hr
      · split at hr
        · injection hr with hr
          rcases hw with rfl | rfl
          · exact hr.symm
          · omega
        · injection hr with hr
          rcases hw with rfl | rfl
          · omega
          · exact hr.symm
    · rw [decision_three (by rw [hv]; simp)] at hr
      exact absurd hr lowestDecision_ne_winner
  | @step S e rds w0 hr hrest ih =>
    intro hSn w hw hm
    have hz : ∀ i ∈ e.eliminated, i ≠ w := by
      intro i hi hiw
      subst hiw
      rcases decision_eq_eliminate hr with ⟨h3, hl⟩ | ⟨x, y, hv, hxy, -⟩
      · obtain ⟨z, hzS, hez, hmin⟩ := lowest_min (List.ne_nil_of_mem hw) hl
        rw [hez, List.mem_singleton] at hi
        subst hi
        rw [Holder.votes_length] at h3
        obtain ⟨y, hyS, hyz⟩ := Holder.exists_ne hSn (by omega) i
        have := hmin y hyS
        have := two_le_continuing (interpret kinds) ballots hSn hw hyS (Ne.symm hyz)
        omega
      · have hv' := hv
        rw [votes_eq] at hv'
        rw [continuing_eq_sum] at hm
        rcases S with _ | ⟨a, _ | ⟨b, _ | ⟨c, S⟩⟩⟩
        · simp at hw
        · simp at hv'
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv'
          obtain ⟨rfl, rfl⟩ := hv'
          simp only at hxy
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hm
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
          rcases hw with rfl | rfl <;> omega
        · simp at hv'
    have hw1 : w ∈ S.filter fun i : Nat => decide (i ∉ e.eliminated) :=
      List.mem_filter.2 ⟨hw, by simpa using fun h => hz w h rfl⟩
    have hS1 : (S.filter fun i : Nat => decide (i ∉ e.eliminated)).Nodup :=
      List.filter_sublist.nodup hSn
    have hm1 := majority_subset (interpret_closed kinds) (interpret_stable kinds) hSn hS1
      List.filter_sublist.subset ballots hw1 hm
    obtain ⟨h1, h2⟩ := ih hS1 hw1 hm1
    refine ⟨?_, h2⟩
    intro rd hrd
    rcases List.mem_cons.1 hrd with rfl | hrd
    · rw [continuingSet_tally]
      exact hw
    · exact h1 rd hrd

/-! ## The initial test -/

/-- Every ballot that ranks a candidate of the continuing set first alone counts for it. -/
theorem firstCount_le_votes {S : List Nat} {w : Nat} (hw : w ∈ S) :
    firstCount ballots w ≤ votesFor (interpret kinds) S ballots w := by
  unfold firstCount votesFor
  rw [List.count_eq_countP, List.count_eq_countP, List.countP_map, List.countP_map]
  apply List.countP_mono_left
  intro ps _ h
  simp only [Function.comp_apply, beq_iff_eq] at h ⊢
  cases ps with
  | nil => simp [firstPosition] at h
  | cons x ps =>
    simp only [firstPosition] at h
    simp [interpret, examine, h, hw]

theorem continuing_le (S : List Nat) (hS : S.Nodup) :
    (tally (interpret kinds) S ballots).continuing ≤ ballots.length := by
  rw [continuing_eq_countP _ _ hS]
  exact List.countP_le_length.trans (by simp)

theorem countWithoutTest_trace (kinds : List Kind) (order : List Nat)
    (ballots : List (List UInt64)) :
    Trace (interpret kinds) (decision order) ballots (countedSet kinds)
      (countWithoutTest kinds order ballots).rounds (countWithoutTest kinds order ballots).winner :=
  run_trace (decision_ends order) _ _ (by omega) (by omega)

theorem singleCount_trace (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    Trace (interpret kinds) (ruleSingle order) ballots (countedSet kinds)
      (singleCount kinds order ballots).rounds (singleCount kinds order ballots).winner :=
  run_trace (ruleSingle_ends order) _ _ (by omega) (by omega)

/-! ## The single count -/

/-- A round of the single count that eliminates is decided by rule 4 with no majority and a
continuing ballot. -/
theorem ruleSingle_eliminate {t : Tally} {e : Elimination} (h : ruleSingle order t = .eliminate e) :
    (∀ x ∈ t.votes, ¬ t.continuing < 2 * x.2) ∧ t.continuing ≠ 0 ∧
      lowestDecision order (ruleTied t.votes) = .eliminate e := by
  unfold ruleSingle at h
  split at h
  · cases h
  · rename_i hf
    by_cases h0 : t.continuing = 0
    · rw [ite_eq_left h0] at h
      cases h
    · rw [ite_eq_right h0] at h
      refine ⟨fun x hx hlt => ?_, h0, h⟩
      have := List.find?_eq_none.mp hf x hx
      simp [hlt] at this

/-- A round of the single count that eliminates is decided by `decision` in the same way. -/
theorem decision_of_single {t : Tally} {e : Elimination} (h : ruleSingle order t = .eliminate e) :
    decision order t = .eliminate e := by
  obtain ⟨hmaj, h0, hl⟩ := ruleSingle_eliminate h
  rcases Nat.lt_or_ge t.votes.length 3 with hl3 | hl3
  · have hT : t.continuing = (t.votes.map fun x : Nat × Nat => x.2).sum := rfl
    match hv : t.votes, hl3 with
    | [], _ =>
      rw [hv] at hT
      exact absurd hT h0
    | [x], _ =>
      rw [hv] at hT hmaj
      have := hmaj x (by simp)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hT
      omega
    | [x, y], _ =>
      rw [hv] at hT hmaj
      have hx := hmaj x (by simp)
      have hy := hmaj y (by simp)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hT
      have hxy : x.2 = y.2 := by omega
      rw [decision_two hv, ite_eq_left hxy, ← hl, hv, ruleTied_eq_fewest]
      have hf : fewest [x, y] = [x.1, y.1] := by
        simp [fewest, hxy]
      rw [hf, lowestDecision_of_ne (by simp)]
  · rw [decision_three hl3, hl]

/-- While the single count runs from a set, the count without the initial test from the same set
has the same rounds, and when the single count names `w`, so does the count. -/
theorem single_names :
    ∀ {C : List Nat} {rds : List Round} {w : Nat},
      Trace (interpret kinds) (ruleSingle order) ballots C rds (some w) → C.Nodup →
      ∀ {rds' : List Round} {w' : Option Nat},
        Trace (interpret kinds) (decision order) ballots C rds' w' → w' = some w := by
  intro C rds w ht
  generalize hw : some w = w0 at ht
  induction ht with
  | @last C w0 hr =>
    intro hC rds' w' hm
    subst hw
    unfold ruleSingle at hr
    split at hr
    · rename_i x hx
      injection hr with hr
      injection hr with hr
      subst hr
      have hT := List.find?_some hx
      have hxm := List.mem_of_find?_eq_some hx
      obtain ⟨hxC, hxv⟩ := mem_votes.1 (show (x.1, x.2) ∈ (tally (interpret kinds) C ballots).votes
        from hxm)
      have hmaj : (tally (interpret kinds) C ballots).continuing <
          2 * votesFor (interpret kinds) C ballots x.1 := by
        rw [← hxv]
        simpa using hT
      exact (holder_trace hm hC hxC hmaj).2
    · split at hr
      · injection hr with hr
        cases hr
      · exact absurd hr lowestDecision_ne_winner
  | @step C e rds w0 hr hrest ih =>
    intro hC rds' w' hm
    have hd := decision_of_single hr
    cases hm with
    | last h' =>
      rw [hd] at h'
      cases h'
    | step h' hrest' =>
      rw [hd] at h'
      injection h' with h'
      subst h'
      exact ih hw (List.filter_sublist.nodup hC) hrest'

/-! ## T11 -/

/-- T11(a): if `w` holds a majority of the continuing ballots against the continuing set `S`, it
holds a majority against every continuing set `S'` with `w ∈ S' ⊆ S`. -/
theorem holder_subset (kinds : List Kind) (ballots : List (List UInt64)) {S S' : List Nat}
    (hS : S.Nodup) (hS' : S'.Nodup) (hsub : S' ⊆ S) {w : Nat} (hw : w ∈ S')
    (h : (tally (interpret kinds) S ballots).continuing <
      2 * votesFor (interpret kinds) S ballots w) :
    (tally (interpret kinds) S' ballots).continuing < 2 * votesFor (interpret kinds) S' ballots w :=
  majority_subset (interpret_closed kinds) (interpret_stable kinds) hS hS' hsub ballots hw h

/-- T11(b): a candidate that holds more than half of `Tᵣ` in a round of the count continues in
every later round, and the count names it. -/
theorem count_majority (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {p q : List Round} {rd : Round} {w v : Nat}
    (h : (count kinds order ballots).rounds = p ++ rd :: q) (hv : (w, v) ∈ rd.tally.votes)
    (hm : rd.tally.continuing < 2 * v) :
    (∀ rd' ∈ q, w ∈ continuingSet rd') ∧ (count kinds order ballots).winner = some w := by
  cases hi : initialWinner kinds ballots with
  | some w0 =>
    rw [rounds_of_initial hi] at h
    simp at h
  | none =>
    have ht := count_trace (order := order) hi
    have hsuf := trace_suffix p ht h
    obtain ⟨htally, hsubC, -⟩ := ht.mem rd (by rw [h]; simp)
    have hSn := hsubC.nodup (countedSet_nodup kinds)
    rw [htally] at hv hm
    obtain ⟨hw, rfl⟩ := mem_votes.1 hv
    obtain ⟨h1, h2⟩ := holder_trace hsuf hSn hw hm
    exact ⟨fun rd' hrd' => h1 rd' (List.mem_cons_of_mem rd hrd'), h2⟩

/-- T11(c): if the initial test elects `w`, then `w` holds more than half of `T₁` in round 1 of
the count without the initial test, and that count names `w`. -/
theorem initial_holder {w : Nat} (h : initialWinner kinds ballots = some w) :
    (∃ rd v, (countWithoutTest kinds order ballots).rounds.head? = some rd ∧
      (w, v) ∈ rd.tally.votes ∧ rd.tally.continuing < 2 * v) ∧
      (countWithoutTest kinds order ballots).winner = some w := by
  obtain ⟨hwK, hf⟩ := initialWinner_spec h
  have ht := countWithoutTest_trace kinds order ballots
  have hK := countedSet_nodup kinds
  have hle := firstCount_le_votes (kinds := kinds) (ballots := ballots) hwK
  have hT := continuing_le (kinds := kinds) (ballots := ballots) _ hK
  have hm : (tally (interpret kinds) (countedSet kinds) ballots).continuing <
      2 * votesFor (interpret kinds) (countedSet kinds) ballots w := by
    omega
  refine ⟨?_, (holder_trace ht hK hwK hm).2⟩
  obtain ⟨e0, rest, hcons⟩ := trace_cons ht
  refine ⟨_, _, by rw [hcons]; rfl, mem_votes.2 ⟨hwK, rfl⟩, hm⟩

/-- T11(d): if the single count names `w`, the count names `w`. -/
theorem single_winner {w : Nat} (h : (singleCount kinds order ballots).winner = some w) :
    (count kinds order ballots).winner = some w := by
  have hs := singleCount_trace kinds order ballots
  rw [h] at hs
  have hw := single_names hs (countedSet_nodup kinds) (countWithoutTest_trace kinds order ballots)
  cases hi : initialWinner kinds ballots with
  | none => exact (count_run (order := order) hi).symm ▸ hw
  | some w0 =>
    rw [count_initial hi]
    have h0 := (initial_holder (order := order) hi).2
    rw [hw] at h0
    exact h0.symm ▸ rfl

#print axioms holder_subset
#print axioms count_majority
#print axioms initial_holder
#print axioms single_winner

end Demos.Rcv.Maine
