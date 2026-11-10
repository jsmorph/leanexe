import Demos.Rcv.Holder

/-!
The properties of instant runoff of [the requirements](requirements.md), section "Properties of
instant runoff": T12 Majority criterion, T13 Condorcet loser, T14 Later-no-harm, and T15
Monotonicity fails, over the count of `Demos.Rcv.Spec`.  The properties compare ballots through
the interpretation: `Beats` states that more ballots count for one candidate than for another
against the continuing set of the two, and `Raises` that a ballot's position marking only one
candidate moves to an earlier position while the other positions keep their order.

T12 takes the county count's winner from `Demos.Rcv.Holder.county_holder`, the form of T11(b) over
traces.  `trace_not_loser` proves T13 over traces of the count for every interpretation that
satisfies `Demos.Rcv.Stability.Closed` and `Demos.Rcv.Stability.Stable`.  When two or more
candidates continue in the last round, the winner's majority persists by T11(a) against the pair of
itself and any other candidate, which beats it there.  When the winner continues alone, the round
before eliminated one candidate, since a batch leaves two or more, and that candidate had the
fewest votes against a set with the members of the pair of it and the winner, against which it
beats the winner.  For T14, `interpret_prefix` shows that a ballot whose position marks only a
continuing candidate has an interpretation that its positions up to that one determine,
`trace_winner_all` that the count's winner continues in every round, and `trace_ballots`, for
every interpretation and decision, that ballots giving every round of a trace the same counts give
the same trace.  T15 evaluates the two contests and their constraints in the kernel.
-/

namespace Demos.Rcv.Properties

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Stability Demos.Rcv.Variants
  Demos.Rcv.Batch Demos.Rcv.Holder

/-! ## Terms of the properties -/

/-- `a` beats `b`: more ballots count for `a` than for `b` against the continuing set `{a, b}`. -/
def Beats (kinds : List Kind) (ballots : List (List UInt64)) (a b : Nat) : Prop :=
  (ballots.countP fun ps : List UInt64 => interpret kinds [a, b] ps == .counts b) <
    ballots.countP fun ps : List UInt64 => interpret kinds [a, b] ps == .counts a

/-- The positions `ps'` raise the candidate `w` on the positions `ps`: they move a position of
`ps` that marks only `w` to an earlier position and leave the other positions in their order. -/
def Raises (w : Nat) (ps ps' : List UInt64) : Prop :=
  ∃ (pre mid post : List UInt64) (x : UInt64), mid ≠ [] ∧ position x = .single w ∧
    ps = pre ++ mid ++ x :: post ∧ ps' = pre ++ x :: (mid ++ post)

/-! ## Votes -/

variable {interp : Interp} {ballots : List (List UInt64)}

theorem votesFor_eq_countP (interp : Interp) (S : List Nat) (ballots : List (List UInt64))
    (w : Nat) :
    votesFor interp S ballots w =
      ballots.countP fun ps : List UInt64 => interp S ps == .counts w := by
  unfold votesFor List.count
  rw [List.countP_map]
  rfl

/-- An interpretation that satisfies T8 and counts only for members of the set gives the same
outcome against two sets with the same members. -/
theorem interp_congr (hI : Closed interp) (hS : Stable interp) {S S' : List Nat} (h1 : S ⊆ S')
    (h2 : S' ⊆ S) (ps : List UInt64) : interp S ps = interp S' ps := by
  cases h : interp S ps with
  | counts w => exact (hS.1 S S' ps w h2 h (h1 (hI S ps w h))).symm
  | inactive r => exact (hS.2 S S' ps r h2 h).symm

theorem votesFor_congr (hI : Closed interp) (hS : Stable interp) {S S' : List Nat} (h1 : S ⊆ S')
    (h2 : S' ⊆ S) (ballots : List (List UInt64)) (w : Nat) :
    votesFor interp S ballots w = votesFor interp S' ballots w := by
  unfold votesFor
  rw [List.map_congr_left fun ps _ => interp_congr hI hS h1 h2 ps]

theorem eq_of_length_le_one {l : List Nat} (h : l.length ≤ 1) {a b : Nat} (ha : a ∈ l)
    (hb : b ∈ l) : a = b := by
  match l, h, ha, hb with
  | [], _, ha, _ => simp at ha
  | [y], _, ha, hb =>
    simp only [List.mem_singleton] at ha hb
    rw [ha, hb]
  | _ :: _ :: _, h, _, _ => simp at h

/-! ## Winners of traces -/

/-- The winner of a trace of the count belongs to its first continuing set. -/
theorem trace_winner_mem {order C : List Nat} {rds : List Round} {w : Nat}
    (ht : Trace interp (rule order) ballots C rds (some w)) : w ∈ C := by
  obtain ⟨last, v, hl, hv, -⟩ := trace_holder ht rfl
  obtain ⟨-, hsub, -⟩ := ht.mem last (List.mem_of_getLast? hl)
  exact hsub.subset (List.mem_map.2 ⟨(w, v), hv, rfl⟩)

/-- The winner of a trace of the count continues in every round. -/
theorem trace_winner_all {order C : List Nat} {rds : List Round} {w : Nat}
    (ht : Trace interp (rule order) ballots C rds (some w)) :
    ∀ rd ∈ rds, w ∈ continuingSet rd := by
  intro rd hrd
  obtain ⟨p, q, hpq⟩ := List.append_of_mem hrd
  exact trace_winner_mem (trace_suffix p ht hpq)

/-! ## T12 -/

/-- A candidate that holds a majority against `K` wins the count in round 1, and the single count
and the county count name it. -/
theorem majority_round_one (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {w : Nat}
    (h : (tally (interpret kinds) (countedSet kinds) ballots).continuing <
      2 * votesFor (interpret kinds) (countedSet kinds) ballots w) :
    (count kinds order ballots).rounds.length = 1 ∧
      (count kinds order ballots).winner = some w ∧
      (singleCount kinds order ballots).winner = some w ∧
      (countyCount kinds order ballots).winner = some w := by
  have hK := countedSet_nodup kinds
  have hw : w ∈ countedSet kinds := by
    by_cases hw : w ∈ countedSet kinds
    · exact hw
    · have h0 : votesFor (interpret kinds) (countedSet kinds) ballots w = 0 := by
        unfold votesFor
        rw [List.count_eq_zero]
        intro hm
        obtain ⟨ps, -, hps⟩ := List.mem_map.1 hm
        exact hw (interpret_counts hps)
      omega
  have hr := rule_holder (order := order) hK hw h
  have hs : ruleSingle order (tally (interpret kinds) (countedSet kinds) ballots) =
      .winner (some w) := by
    unfold ruleSingle
    rw [find_holder hK hw h]
  have hc := county_holder (interpret_closed kinds) (interpret_stable kinds)
    (county_trace kinds order ballots) hK hw h
  refine ⟨?_, ?_, ?_, hc.2⟩
  · simp only [count, run, hr, List.length_singleton]
  · simp only [count, run, hr]
  · simp only [singleCount, run, hs]

/-- T12 Majority criterion.  If more than half of the continuing ballots of round 1, those whose
interpretation against the counted set `K` counts for a candidate, count for `w`, the count ends
after round 1 with `w`, and the single count and the county count name `w`. -/
theorem majority_criterion (c : Contest) (w : Nat)
    (h : (tally (interpret (kindsOf c)) (countedSet (kindsOf c))
          (c.ballots.map fun b : Ballot => b.positions)).continuing <
        2 * (c.ballots.map fun b : Ballot => b.positions).countP fun ps : List UInt64 =>
          interpret (kindsOf c) (countedSet (kindsOf c)) ps == .counts w) :
    (countContest c).rounds.length = 1 ∧ (countContest c).winner = some w ∧
      (singleCount (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)).winner =
        some w ∧
      (countyCount (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)).winner =
        some w := by
  rw [← votesFor_eq_countP (interpret (kindsOf c)) (countedSet (kindsOf c))] at h
  exact majority_round_one (kindsOf c) c.order _ h

/-! ## T13 -/

/-- In a trace of the count from a set of two or more candidates, a candidate `ℓ` that every other
candidate of the set beats against the pair of the two is not the winner. -/
theorem trace_not_loser (hI : Closed interp) (hS : Stable interp) {order : List Nat} {ℓ : Nat} :
    ∀ {C : List Nat} {rds : List Round} {w : Option Nat},
      Trace interp (rule order) ballots C rds w → C.Nodup → 2 ≤ C.length →
      (∀ a ∈ C, a ≠ ℓ →
        votesFor interp [a, ℓ] ballots ℓ < votesFor interp [a, ℓ] ballots a) →
      w ≠ some ℓ := by
  intro C rds w ht
  induction ht with
  | @last C w hr =>
    intro hC h2 hb hw
    subst hw
    rcases rule_eq_winner hr with ⟨⟨i, v⟩, hx, hm, hxw⟩ | ⟨-, hn⟩
    · obtain ⟨hl, rfl⟩ := mem_votes.1 hx
      have hil : ℓ = i := by simpa using hxw
      subst hil
      obtain ⟨a, ha, hal⟩ := exists_ne hC h2 ℓ
      have hsub : [a, ℓ] ⊆ C := by
        intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl
        · exact ha
        · exact hl
      have hnd : [a, ℓ].Nodup := by simp [hal]
      have hm' := majority_subset hI hS hC hnd hsub ballots (by simp) hm
      have h2' := two_le_continuing interp ballots hnd (by simp) (by simp) hal
      have := hb a ha hal
      omega
    · cases hn
  | @step C e rds w hr hrest ih =>
    intro hC h2 hb hw
    subst hw
    have hC' : (C.filter fun i : Nat => decide (i ∉ e.eliminated)).Nodup :=
      List.filter_sublist.nodup hC
    by_cases h2' : 2 ≤ (C.filter fun i : Nat => decide (i ∉ e.eliminated)).length
    · exact ih hC' h2' (fun a ha hal => hb a (List.mem_filter.1 ha).1 hal) rfl
    · have hl := trace_winner_mem hrest
      obtain ⟨hlC, hle⟩ := List.mem_filter.1 hl
      by_cases hbat : ∃ B, e = .batch B
      · obtain ⟨B, rfl⟩ := hbat
        obtain ⟨X, hbx⟩ := batchAt_of_rule hC hr
        exact h2' hbx.rest_two_le
      · have hnb : ∀ s, e ≠ .batch s := fun s h => hbat ⟨s, h⟩
        obtain ⟨z, hzC, hez, hmin⟩ := lowest_min (List.ne_nil_of_mem hlC) (rule_lowest hr hnb)
        have hzl : z ≠ ℓ := by
          intro hzl
          subst hzl
          simp [hez] at hle
        have hsub1 : C ⊆ [z, ℓ] := by
          intro i hi
          by_cases hiz : i = z
          · simp [hiz]
          · have hi' : i ∈ C.filter fun i : Nat => decide (i ∉ e.eliminated) :=
              List.mem_filter.2 ⟨hi, by simp [hez, hiz]⟩
            simp [eq_of_length_le_one (by omega) hi' hl]
        have hsub2 : [z, ℓ] ⊆ C := by
          intro i hi
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
          rcases hi with rfl | rfl
          · exact hzC
          · exact hlC
        have e1 := votesFor_congr hI hS hsub1 hsub2 ballots z
        have e2 := votesFor_congr hI hS hsub1 hsub2 ballots ℓ
        have := hmin ℓ hlC
        have := hb z hzC hzl
        omega

/-- T13 Condorcet loser.  If the counted set `K` has two or more candidates and every other
candidate of `K` beats `ℓ`, the count does not name `ℓ`. -/
theorem condorcet_loser (c : Contest) (ℓ : Nat) (hK : 2 ≤ (countedSet (kindsOf c)).length)
    (h : ∀ a ∈ countedSet (kindsOf c), a ≠ ℓ →
      Beats (kindsOf c) (c.ballots.map fun b : Ballot => b.positions) a ℓ) :
    (countContest c).winner ≠ some ℓ :=
  trace_not_loser (interpret_closed _) (interpret_stable _) (count_trace _ _ _)
    (countedSet_nodup _) hK fun a ha hal => by
      have hb := h a ha hal
      unfold Beats at hb
      rw [votesFor_eq_countP, votesFor_eq_countP]
      exact hb

/-! ## T14 -/

/-- When `x`, after the positions `pre`, marks only a member `w` of `C`, the examination against
`C` ends at or before `x`, so the positions after `x` do not enter it. -/
theorem examine_prefix {C : List Nat} {w : Nat} (hw : w ∈ C) {x : UInt64}
    (hx : position x = .single w) :
    ∀ (pre post post' : List UInt64),
      examine C (pre ++ x :: post) = examine C (pre ++ x :: post') ∧
        (examine C (pre ++ x :: post)).isSome = true
  | [], post, post' => by simp [examine, hx, hw]
  | y :: pre, post, post' => by
    obtain ⟨h1, h2⟩ := examine_prefix hw hx pre post post'
    cases hy : position y with
    | empty =>
      simp only [List.cons_append, examine, hy]
      exact ⟨h1, h2⟩
    | multiple => simp [examine, hy]
    | single i =>
      simp only [List.cons_append, examine, hy]
      by_cases hi : i ∈ C
      · simp [hi]
      · simp only [ite_eq_right hi]
        exact ⟨h1, h2⟩

/-- A ballot whose position after `pre` marks only a member `w` of `C` has an interpretation
against `C` that its positions up to that one determine. -/
theorem interpret_prefix (kinds : List Kind) {C : List Nat} {w : Nat} (hw : w ∈ C) {x : UInt64}
    (hx : position x = .single w) (pre post post' : List UInt64) :
    interpret kinds C (pre ++ x :: post') = interpret kinds C (pre ++ x :: post) := by
  obtain ⟨h1, h2⟩ := examine_prefix hw hx pre post post'
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h2
  unfold interpret
  rw [← h1, ho, Option.getD_some, Option.getD_some]

/-- Ballots that give each round of a trace the counts of the trace's ballots give the same
trace. -/
theorem trace_ballots {decision : Tally → Decision} {ballots' : List (List UInt64)} :
    ∀ {C : List Nat} {rds : List Round} {w : Option Nat},
      Trace interp decision ballots C rds w →
      (∀ rd ∈ rds, tally interp (continuingSet rd) ballots' =
        tally interp (continuingSet rd) ballots) →
      Trace interp decision ballots' C rds w := by
  intro C rds w ht
  induction ht with
  | @last C w hr =>
    intro h
    have heq := h _ List.mem_cons_self
    rw [continuingSet_tally] at heq
    rw [← heq] at hr ⊢
    exact Trace.last hr
  | @step C e rds w hr hrest ih =>
    intro h
    have heq := h _ List.mem_cons_self
    rw [continuingSet_tally] at heq
    have hrest' := ih fun rd hrd => h rd (List.mem_cons_of_mem _ hrd)
    rw [← heq] at hr ⊢
    exact Trace.step hr hrest'

theorem tally_replace (C : List Nat) (pre post : List (List UInt64)) {ps ps' : List UInt64}
    (h : interp C ps' = interp C ps) :
    tally interp C (pre ++ ps' :: post) = tally interp C (pre ++ ps :: post) := by
  simp only [tally, List.map_append, List.map_cons, h]

/-- T14 Later-no-harm.  Let position `p` of a ballot `b` mark only `w`, and replace `b` with a
ballot `b'` whose positions 1 to `p` are those of `b`.  If the count of the first contest names
`w`, the count of the second has the same rounds and names `w`.  The premise that the count names
`w` makes `w` a counted candidate. -/
theorem later_no_harm (c : Contest) (pre post : List Ballot) (b b' : Ballot) (p w : Nat)
    (x : UInt64) (hc : c.ballots = pre ++ b :: post) (hp : 1 ≤ p)
    (hx : b.positions[p - 1]? = some x) (hxw : position x = .single w)
    (htake : b'.positions.take p = b.positions.take p) (hwin : (countContest c).winner = some w) :
    (countContest { c with ballots := pre ++ b' :: post }).rounds = (countContest c).rounds ∧
      (countContest { c with ballots := pre ++ b' :: post }).winner = some w := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hx
  obtain ⟨hq, hxq⟩ := List.getElem?_eq_some_iff.1 hx
  have hb : b.positions = b.positions.take q ++ x :: b.positions.drop (q + 1) := by
    have := List.take_append_drop q b.positions
    rw [List.drop_eq_getElem_cons hq, hxq] at this
    exact this.symm
  have hb' : b'.positions = b.positions.take q ++ x :: b'.positions.drop (q + 1) := by
    have := List.take_append_drop (q + 1) b'.positions
    rw [htake, List.take_add_one, hx] at this
    simpa using this.symm
  have ht := count_trace (kindsOf c) c.order (c.ballots.map fun a : Ballot => a.positions)
  have hrw : (count (kindsOf c) c.order (c.ballots.map fun a : Ballot => a.positions)).winner =
      some w := hwin
  rw [hrw] at ht
  have hall := trace_winner_all ht
  have ht' : Trace (interpret (kindsOf c)) (rule c.order)
      ((pre ++ b' :: post).map fun a : Ballot => a.positions) (countedSet (kindsOf c))
      (count (kindsOf c) c.order (c.ballots.map fun a : Ballot => a.positions)).rounds
      (some w) := by
    apply trace_ballots ht
    intro rd hrd
    simp only [hc, List.map_append, List.map_cons]
    apply tally_replace
    have h := interpret_prefix (kindsOf c) (hall rd hrd) hxw (b.positions.take q)
      (b.positions.drop (q + 1)) (b'.positions.drop (q + 1))
    rwa [← hb', ← hb] at h
  exact trace_unique
    (count_trace (kindsOf c) c.order ((pre ++ b' :: post).map fun a : Ballot => a.positions)) ht'

/-! ## T15 -/

/-- The contests of T15: candidates `A`, `B`, and `C`, all listed, three positions, the order
`1 2 3`, and 17 ballots, six `1,2,3`, five `2,1,3`, four `3,2,1`, and two with the positions
`last`.  The position words of candidates 1, 2, and 3 are 1, 2, and 4. -/
def monotonicityContest (last : List UInt64) : Contest :=
  { contest := ascii "t15"
    positions := 3
    candidates := [⟨.listed, ascii "A"⟩, ⟨.listed, ascii "B"⟩, ⟨.listed, ascii "C"⟩]
    order := [1, 2, 3]
    ballots := (List.replicate 6 [1, 2, 4] ++ List.replicate 5 [2, 1, 4] ++
        List.replicate 4 [4, 2, 1] ++ List.replicate 2 last).map fun ps : List UInt64 =>
      { ident := none, positions := ps } }

/-- T15 Monotonicity fails.  The first contest's two last ballots are `3,1,2`, and the second
replaces them with `1,3,2`, which raise `A` from the second position to the first.  Both contests
meet the constraints, and the count names `A` for the first and `B` for the second.  Round 1 of
each eliminates the one candidate with the fewest votes, `B` in the first and `C` in the second,
so neither count marks a tie.  The kernel evaluates the counts. -/
theorem monotonicity_fails :
    (monotonicityContest [4, 1, 2]).WellFormed ∧ (monotonicityContest [1, 4, 2]).WellFormed ∧
      (∃ (same : List Ballot) (b b' : Ballot),
        (monotonicityContest [4, 1, 2]).ballots = same ++ [b, b] ∧
        monotonicityContest [1, 4, 2] =
          { monotonicityContest [4, 1, 2] with ballots := same ++ [b', b'] } ∧
        Raises 1 b.positions b'.positions) ∧
      (countContest (monotonicityContest [4, 1, 2])).winner = some 1 ∧
      (countContest (monotonicityContest [1, 4, 2])).winner = some 2 ∧
      (countContest (monotonicityContest [4, 1, 2])).rounds.map Round.elimination =
        [some (.lowest 2), none] ∧
      (countContest (monotonicityContest [1, 4, 2])).rounds.map Round.elimination =
        [some (.lowest 3), none] := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  refine ⟨((List.replicate 6 [1, 2, 4] ++ List.replicate 5 [2, 1, 4] ++
      List.replicate 4 [4, 2, 1] : List (List UInt64))).map fun ps : List UInt64 =>
        { ident := none, positions := ps },
    ⟨none, [4, 1, 2]⟩, ⟨none, [1, 4, 2]⟩, rfl, rfl, ?_⟩
  exact ⟨[], [4], [2], 1, by simp, by decide +kernel, rfl, rfl⟩

end Demos.Rcv.Properties
