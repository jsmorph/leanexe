import Demos.Rcv.Maine.Holder
import Demos.Rcv.Properties

/-!
T12 Majority criterion, T13 Condorcet loser, T14 Later-no-harm, and T15 Monotonicity fails of
[the requirements](requirements.md), section "Theorems", for the Maine count.  `Beats` states the
requirements' term "beats" through this module's interpretation.

T12 has two parts.  A candidate of `K` ranked first alone on more than half of the ballots holds a
majority of round 1 of the count without the initial test (`firstCount_le_votes`), and so does
every winner of the test, so the test elects it (`initialWinner_of_first`), since at most one
candidate holds a majority.  A candidate that holds a majority of round 1 of the count without the
initial test is named by that count (`holder_trace`), and by the count, whose initial test elects
only that candidate when it elects one (`initial_holder`).

`trace_not_loser` proves T13 over traces of `decision`.  The last round has two candidates, and the
one with more votes against the pair wins, which the other beats.  When the winner continues alone,
the round before eliminated one candidate with the fewest votes (`decision_fewest`), against a set
with the members of the pair of it and the winner, against which it beats the winner.  The initial
test cannot elect `ℓ`: the ballots that rank `ℓ` first alone count for `ℓ` against every pair that
holds it.

For T14, `interpret_prefix` shows that a ballot whose position marks only a continuing candidate has
an interpretation that its positions up to that one determine: rule 1 of the interpretation at an
earlier empty position reads the later positions only for a mark, and that position is marked.  The
two contests have the same first positions, so the initial test decides both or neither, and
otherwise the Oakland lemmas `Demos.Rcv.Properties.trace_ballots` and
`Demos.Rcv.Properties.tally_replace` carry the trace of the first count to the second.  T15
evaluates the two counts of the Oakland contests in the kernel and takes the constraints and the
raised ballots from `Demos.Rcv.Properties.monotonicity_fails`.
-/

namespace Demos.Rcv.Maine

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Stability

/-- `a` beats `b`: more ballots count for `a` than for `b` against the continuing set `{a, b}`,
under this module's interpretation. -/
def Beats (kinds : List Kind) (ballots : List (List UInt64)) (a b : Nat) : Prop :=
  (ballots.countP fun ps : List UInt64 => interpret kinds [a, b] ps == .counts b) <
    ballots.countP fun ps : List UInt64 => interpret kinds [a, b] ps == .counts a

variable {kinds : List Kind} {order : List Nat} {ballots : List (List UInt64)}

/-! ## T12 -/

theorem firstCount_eq_countP (ballots : List (List UInt64)) (w : Nat) :
    firstCount ballots w = ballots.countP (FirstMarks w) := by
  unfold firstCount
  rw [List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro ps _
  cases ps with
  | nil => simp [firstPosition, FirstMarks]
  | cons w ws => simp [firstPosition, FirstMarks]

/-- The initial test elects a candidate of `K` that is ranked first alone on more than half of the
ballots. -/
theorem initialWinner_of_first {w : Nat} (hw : w ∈ countedSet kinds)
    (h : ballots.length < 2 * firstCount ballots w) : initialWinner kinds ballots = some w := by
  have hK := countedSet_nodup kinds
  have hm : ∀ {v : Nat}, v ∈ countedSet kinds → ballots.length < 2 * firstCount ballots v →
      (tally (interpret kinds) (countedSet kinds) ballots).continuing <
        2 * votesFor (interpret kinds) (countedSet kinds) ballots v := by
    intro v hv hf
    have := firstCount_le_votes (kinds := kinds) (ballots := ballots) hv
    have := continuing_le (kinds := kinds) (ballots := ballots) _ hK
    omega
  cases hi : initialWinner kinds ballots with
  | some v =>
    obtain ⟨hv, hf⟩ := initialWinner_spec hi
    rw [majority_unique (interpret kinds) ballots hK hv hw (hm hv hf) (hm hw h)]
  | none =>
    exfalso
    unfold initialWinner at hi
    rw [firstCounts_eq, Option.map_eq_none_iff, List.find?_eq_none] at hi
    have := hi (w, firstCount ballots w) (List.mem_map.2 ⟨w, hw, rfl⟩)
    simp [h] at this

/-- A candidate that holds more than half of the continuing ballots of round 1 of the count without
the initial test, those against `K`, is the count's winner. -/
theorem majority_round_one {w : Nat}
    (h : (tally (interpret kinds) (countedSet kinds) ballots).continuing <
      2 * votesFor (interpret kinds) (countedSet kinds) ballots w) :
    (count kinds order ballots).winner = some w := by
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
  have hn := (holder_trace (countWithoutTest_trace kinds order ballots) hK hw h).2
  cases hi : initialWinner kinds ballots with
  | none => exact (count_run (order := order) hi).symm ▸ hn
  | some v =>
    rw [count_initial hi]
    have hv := (initial_holder (order := order) hi).2
    rw [hn] at hv
    exact hv.symm

/-- T12 Majority criterion.  If more than half of the ballots rank a candidate `w` of `K` first
alone, the count ends by the initial test with `w` and no rounds.  If more than half of the
continuing ballots of round 1 of the count without the initial test, the round against `K`, count
for `w`, the count names `w`. -/
theorem majority_criterion (c : Contest) (w : Nat) :
    (w ∈ countedSet (kindsOf c) →
      c.ballots.length < 2 * (positionsOf c).countP (FirstMarks w) →
      (countContest c).rounds = [] ∧ (countContest c).winner = some w) ∧
    ((tally (interpret (kindsOf c)) (countedSet (kindsOf c)) (positionsOf c)).continuing <
        2 * (positionsOf c).countP (fun ps : List UInt64 =>
          interpret (kindsOf c) (countedSet (kindsOf c)) ps == .counts w) →
      (countContest c).winner = some w) := by
  refine ⟨fun hw h => ?_, fun h => ?_⟩
  · have hlen : (positionsOf c).length = c.ballots.length := by simp [positionsOf]
    rw [← firstCount_eq_countP, ← hlen] at h
    have hi := initialWinner_of_first hw h
    show (count (kindsOf c) c.order (positionsOf c)).rounds = [] ∧
      (count (kindsOf c) c.order (positionsOf c)).winner = some w
    rw [count_initial hi]
    exact ⟨rfl, rfl⟩
  · rw [← Properties.votesFor_eq_countP] at h
    exact majority_round_one h

/-! ## T13 -/

/-- An elimination of `decision` names one candidate of the round with the fewest votes. -/
theorem decision_fewest {C : List Nat} {e : Elimination} (hC : C ≠ [])
    (h : decision order (tally (interpret kinds) C ballots) = .eliminate e) :
    ∃ z ∈ C, e.eliminated = [z] ∧
      ∀ j ∈ C, votesFor (interpret kinds) C ballots z ≤ votesFor (interpret kinds) C ballots j := by
  rcases decision_eq_eliminate h with ⟨-, hl⟩ | ⟨x, y, hv, hxy, rfl⟩
  · exact Batch.lowest_min hC hl
  · rw [votes_eq] at hv
    rcases C with _ | ⟨a, _ | ⟨b, _ | ⟨d, C⟩⟩⟩
    · exact absurd rfl hC
    · simp at hv
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv
      obtain ⟨rfl, rfl⟩ := hv
      simp only at hxy
      have hz := latest_mem (order := order) (Z := [a, b]) (by simp)
      refine ⟨_, hz, rfl, fun j hj => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz hj
      rcases hz with hz | hz <;> rcases hj with rfl | rfl <;> rw [hz] <;> omega
    · simp at hv

/-- In a trace of `decision` from a set of two or more candidates, a candidate `ℓ` that every other
candidate of the set beats against the pair of the two is not the winner. -/
theorem trace_not_loser {ℓ : Nat} :
    ∀ {C : List Nat} {rds : List Round} {w : Option Nat},
      Trace (interpret kinds) (decision order) ballots C rds w → C.Nodup → 2 ≤ C.length →
      (∀ a ∈ C, a ≠ ℓ →
        votesFor (interpret kinds) [a, ℓ] ballots ℓ < votesFor (interpret kinds) [a, ℓ] ballots a) →
      w ≠ some ℓ := by
  intro C rds w ht
  induction ht with
  | @last C w hr =>
    intro hC h2 hb hw
    subst hw
    have hlen := Holder.votes_length (interpret kinds) C ballots
    have hkeys := tally_votes_fst (interpret kinds) C ballots
    rcases decision_eq_winner hr with ⟨hv, -⟩ | ⟨x, -, hv, -⟩ |
        ⟨⟨x1, x2⟩, hx, ⟨y1, y2⟩, hy, hv, ⟨hyx, hw⟩ | ⟨hxy, hw⟩⟩
    · rw [← hlen, hv] at h2
      simp at h2
    · rw [← hlen, hv] at h2
      simp at h2
    · rw [hv] at hkeys
      simp only [List.map_cons, List.map_nil] at hkeys
      subst hkeys
      have hl : x1 = ℓ := (Option.some.inj hw).symm
      subst hl
      obtain ⟨-, hx2⟩ := mem_votes.1 hx
      obtain ⟨hyC, hy2⟩ := mem_votes.1 hy
      have hne : y1 ≠ x1 := by
        intro h
        subst h
        simp at hC
      have hs1 : [x1, y1] ⊆ [y1, x1] := by
        intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi ⊢
        tauto
      have hs2 : [y1, x1] ⊆ [x1, y1] := by
        intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi ⊢
        tauto
      have e1 := Properties.votesFor_congr (interpret_closed kinds) (interpret_stable kinds) hs1 hs2
        ballots x1
      have e2 := Properties.votesFor_congr (interpret_closed kinds) (interpret_stable kinds) hs1 hs2
        ballots y1
      have := hb y1 hyC hne
      omega
    · rw [hv] at hkeys
      simp only [List.map_cons, List.map_nil] at hkeys
      subst hkeys
      have hl : y1 = ℓ := (Option.some.inj hw).symm
      subst hl
      obtain ⟨hxC, hx2⟩ := mem_votes.1 hx
      obtain ⟨-, hy2⟩ := mem_votes.1 hy
      have hne : x1 ≠ y1 := by
        intro h
        subst h
        simp at hC
      have := hb x1 hxC hne
      omega
  | @step C e rds w hr hrest ih =>
    intro hC h2 hb hw
    subst hw
    have hC' : (C.filter fun i : Nat => decide (i ∉ e.eliminated)).Nodup :=
      List.filter_sublist.nodup hC
    by_cases h2' : 2 ≤ (C.filter fun i : Nat => decide (i ∉ e.eliminated)).length
    · exact ih hC' h2' (fun a ha hal => hb a (List.mem_filter.1 ha).1 hal) rfl
    · have hl := trace_winner_mem hrest ℓ rfl
      obtain ⟨hlC, hle⟩ := List.mem_filter.1 hl
      obtain ⟨z, hzC, hez, hmin⟩ := decision_fewest (List.ne_nil_of_mem hlC) hr
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
          simp [Properties.eq_of_length_le_one (by omega) hi' hl]
      have hsub2 : [z, ℓ] ⊆ C := by
        intro i hi
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl
        · exact hzC
        · exact hlC
      have e1 := Properties.votesFor_congr (interpret_closed kinds) (interpret_stable kinds) hsub1
        hsub2 ballots z
      have e2 := Properties.votesFor_congr (interpret_closed kinds) (interpret_stable kinds) hsub1
        hsub2 ballots ℓ
      have := hmin ℓ hlC
      have := hb z hzC hzl
      omega

/-- T13 Condorcet loser.  If the counted set `K` has two or more candidates and every other
candidate of `K` beats `ℓ`, the count does not name `ℓ`. -/
theorem condorcet_loser (c : Contest) (ℓ : Nat) (hK : 2 ≤ (countedSet (kindsOf c)).length)
    (h : ∀ a ∈ countedSet (kindsOf c), a ≠ ℓ → Beats (kindsOf c) (positionsOf c) a ℓ) :
    (countContest c).winner ≠ some ℓ := by
  have hb : ∀ a ∈ countedSet (kindsOf c), a ≠ ℓ →
      votesFor (interpret (kindsOf c)) [a, ℓ] (positionsOf c) ℓ <
        votesFor (interpret (kindsOf c)) [a, ℓ] (positionsOf c) a := fun a ha hal => by
    have hab := h a ha hal
    unfold Beats at hab
    rw [Properties.votesFor_eq_countP, Properties.votesFor_eq_countP]
    exact hab
  show (count (kindsOf c) c.order (positionsOf c)).winner ≠ some ℓ
  cases hi : initialWinner (kindsOf c) (positionsOf c) with
  | none => exact trace_not_loser (count_trace hi) (countedSet_nodup _) hK hb
  | some v =>
    rw [count_initial hi]
    intro hv
    have hvl : v = ℓ := by simpa using hv
    subst hvl
    obtain ⟨hvK, hf⟩ := initialWinner_spec hi
    obtain ⟨a, ha, hav⟩ := Holder.exists_ne (countedSet_nodup _) hK v
    have hnd : [a, v].Nodup := by simp [hav]
    have e1 := firstCount_le_votes (kinds := kindsOf c) (ballots := positionsOf c) (S := [a, v])
      (w := v) (by simp)
    have e2 := two_le_continuing (interpret (kindsOf c)) (positionsOf c) hnd (a := a) (b := v)
      (by simp) (by simp) hav
    have e3 := continuing_le (kinds := kindsOf c) (ballots := positionsOf c) [a, v] hnd
    have e4 := hb a ha hav
    omega

/-! ## T14 -/

/-- When `x`, after the positions `pre`, marks only a member `w` of `C`, the examination against
`C` ends at or before `x`, and the positions after `x` do not enter it: rule 1 at an empty position
of `pre` reads the later positions only for a mark, and `x` is marked. -/
theorem examine_prefix {C : List Nat} {w : Nat} (hw : w ∈ C) {x : UInt64}
    (hx : position x = .single w) :
    ∀ (pre post post' : List UInt64),
      examine C (pre ++ x :: post) = examine C (pre ++ x :: post') ∧
        (examine C (pre ++ x :: post)).isSome = true
  | [], post, post' => by simp [examine, hx, hw]
  | y :: pre, post, post' => by
    obtain ⟨h1, h2⟩ := examine_prefix hw hx pre post post'
    have hxe : (position x == .empty) = false := by
      rw [hx]
      rfl
    have hxm : marked x = true := by
      unfold marked
      rw [hx]
      rfl
    have hs : skipped (pre ++ x :: post) = skipped (pre ++ x :: post') := by
      cases pre with
      | nil => simp only [List.nil_append, skipped, hxe, Bool.false_and]
      | cons z pre =>
        simp only [List.cons_append, skipped, List.any_append, List.any_cons, hxm, Bool.true_or,
          Bool.or_true]
    cases hy : position y with
    | empty =>
      simp only [List.cons_append, examine, hy]
      rw [hs]
      by_cases hk : skipped (pre ++ x :: post') = true
      · rw [ite_eq_left hk, ite_eq_left hk]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hk, ite_eq_right hk]
        exact ⟨h1, h2⟩
    | multiple => simp [examine, hy]
    | single i =>
      simp only [List.cons_append, examine, hy]
      by_cases hi : i ∈ C
      · simp [hi]
      · rw [ite_eq_right hi, ite_eq_right hi]
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

/-- The winner of a trace of `decision` continues in every round. -/
theorem trace_winner_all {C : List Nat} {rds : List Round} {w : Nat}
    (ht : Trace (interpret kinds) (decision order) ballots C rds (some w)) :
    ∀ rd ∈ rds, w ∈ continuingSet rd := by
  intro rd hrd
  obtain ⟨p, q, hpq⟩ := List.append_of_mem hrd
  exact trace_winner_mem (trace_suffix p ht hpq) w rfl

/-- T14 Later-no-harm.  Let position `p` of a ballot `b` mark only `w`, and replace `b` with a
ballot `b'` whose positions 1 to `p` are those of `b`.  If the count of the first contest names
`w`, the count of the second has the same rounds and names `w`.  The first positions of `b` and
`b'` are the same, so the initial test decides both counts or neither. -/
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
  have hfp : firstPosition b'.positions = firstPosition b.positions := by
    have e : ∀ (l r r' : List UInt64), firstPosition (l ++ x :: r) = firstPosition (l ++ x :: r') :=
      fun l r r' => by cases l <;> rfl
    have h := e (b.positions.take q) (b'.positions.drop (q + 1)) (b.positions.drop (q + 1))
    rwa [← hb', ← hb] at h
  have hinit : initialWinner (kindsOf c) (positionsOf { c with ballots := pre ++ b' :: post }) =
      initialWinner (kindsOf c) (positionsOf c) := by
    have hmap : (positionsOf { c with ballots := pre ++ b' :: post }).map firstPosition =
        (positionsOf c).map firstPosition := by
      simp [positionsOf, hc, hfp]
    have hlen : (positionsOf { c with ballots := pre ++ b' :: post }).length =
        (positionsOf c).length := by
      simp [positionsOf, hc]
    simp only [initialWinner, firstCounts, hmap, hlen]
  have hwin' : (count (kindsOf c) c.order (positionsOf c)).winner = some w := hwin
  show (count (kindsOf c) c.order (positionsOf { c with ballots := pre ++ b' :: post })).rounds =
      (count (kindsOf c) c.order (positionsOf c)).rounds ∧
    (count (kindsOf c) c.order (positionsOf { c with ballots := pre ++ b' :: post })).winner =
      some w
  cases hi : initialWinner (kindsOf c) (positionsOf c) with
  | some v =>
    rw [count_initial hi] at hwin' ⊢
    rw [count_initial (hinit.trans hi)]
    exact ⟨rfl, hwin'⟩
  | none =>
    have ht := count_trace (order := c.order) hi
    rw [hwin'] at ht
    have hall := trace_winner_all ht
    have ht' : Trace (interpret (kindsOf c)) (decision c.order)
        (positionsOf { c with ballots := pre ++ b' :: post }) (countedSet (kindsOf c))
        (count (kindsOf c) c.order (positionsOf c)).rounds (some w) := by
      apply Properties.trace_ballots ht
      intro rd hrd
      simp only [positionsOf, hc, List.map_append, List.map_cons]
      apply Properties.tally_replace
      have h := interpret_prefix (kindsOf c) (hall rd hrd) hxw (b.positions.take q)
        (b.positions.drop (q + 1)) (b'.positions.drop (q + 1))
      rwa [← hb', ← hb] at h
    have := trace_unique (count_trace (order := c.order) (hinit.trans hi)) ht'
    exact ⟨this.1, this.2⟩

/-! ## T15 -/

/-- T15 Monotonicity fails.  The contests of the Oakland requirements' T15, which meet the
constraints and differ in two ballots that raise `A` from the second position to the first, have
under this module's count the rounds and the winners of the Oakland count, `A` for the first and
`B` for the second, with the first counts `f(A) = 6`, `f(B) = 5`, `f(C) = 6` and `f(A) = 8`,
`f(B) = 5`, `f(C) = 4` of 17 ballots, so the initial test elects no one.  Round 1 of each
eliminates the one candidate with the fewest votes, `B` in the first and `C` in the second.  The
kernel evaluates the counts. -/
theorem monotonicity_fails :
    (Properties.monotonicityContest [4, 1, 2]).WellFormed ∧
      (Properties.monotonicityContest [1, 4, 2]).WellFormed ∧
      (∃ (same : List Ballot) (b b' : Ballot),
        (Properties.monotonicityContest [4, 1, 2]).ballots = same ++ [b, b] ∧
        Properties.monotonicityContest [1, 4, 2] =
          { Properties.monotonicityContest [4, 1, 2] with ballots := same ++ [b', b'] } ∧
        Properties.Raises 1 b.positions b'.positions) ∧
      countContest (Properties.monotonicityContest [4, 1, 2]) =
        Spec.countContest (Properties.monotonicityContest [4, 1, 2]) ∧
      countContest (Properties.monotonicityContest [1, 4, 2]) =
        Spec.countContest (Properties.monotonicityContest [1, 4, 2]) ∧
      firstContest (Properties.monotonicityContest [4, 1, 2]) = [(1, 6), (2, 5), (3, 6)] ∧
      firstContest (Properties.monotonicityContest [1, 4, 2]) = [(1, 8), (2, 5), (3, 4)] ∧
      (countContest (Properties.monotonicityContest [4, 1, 2])).winner = some 1 ∧
      (countContest (Properties.monotonicityContest [1, 4, 2])).winner = some 2 ∧
      (countContest (Properties.monotonicityContest [4, 1, 2])).rounds.map Round.elimination =
        [some (.lowest 2), none] ∧
      (countContest (Properties.monotonicityContest [1, 4, 2])).rounds.map Round.elimination =
        [some (.lowest 3), none] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := Properties.monotonicity_fails
  have e1 : countContest (Properties.monotonicityContest [4, 1, 2]) =
      Spec.countContest (Properties.monotonicityContest [4, 1, 2]) := by decide +kernel
  have e2 : countContest (Properties.monotonicityContest [1, 4, 2]) =
      Spec.countContest (Properties.monotonicityContest [1, 4, 2]) := by decide +kernel
  refine ⟨h1, h2, h3, e1, e2, by decide +kernel, by decide +kernel, ?_, ?_, ?_, ?_⟩
  · rw [e1]
    exact h4
  · rw [e2]
    exact h5
  · rw [e1]
    exact h6
  · rw [e2]
    exact h7

#print axioms majority_criterion
#print axioms condorcet_loser
#print axioms later_no_harm
#print axioms monotonicity_fails

end Demos.Rcv.Maine
