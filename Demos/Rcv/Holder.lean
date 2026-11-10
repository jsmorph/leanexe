import Demos.Rcv.Batch

/-!
T11 of [the requirements](requirements.md), section "Theorems", which relates the count to the
county count.  (a) is `Demos.Rcv.Stability.majority_subset` for the interpretation of the
requirements.  `county_holder` shows that a candidate that holds a majority in a round of the
county count continues to its end and is named, and `county_rounds` that the rounds of the count
with two or more continuing candidates are rounds of the county count: in a round where the count
eliminates a batch, the county count eliminates its members one per round, as
`Demos.Rcv.Batch.walk` shows, and reaches the count's next round.  `trace_holder` gives the
majority of the count's winner in its last round, and `trace_tied` the tied pair of the round
before a last round with one candidate, which T3 also states.
-/

namespace Demos.Rcv.Holder

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Rounds Demos.Rcv.Stability Demos.Rcv.Variants
  Demos.Rcv.Batch

variable {interp : Interp} {ballots : List (List UInt64)}

/-! ## Decisions -/

theorem votes_length (interp : Interp) (S : List Nat) (ballots : List (List UInt64)) :
    (tally interp S ballots).votes.length = S.length := by
  rw [votes_eq, List.length_map]

/-- A round of the count that eliminates no batch eliminates by rule 4. -/
theorem rule_lowest {order : List Nat} {t : Tally} {e : Elimination}
    (hr : rule order t = .eliminate e) (hnb : ∀ s, e ≠ .batch s) :
    lowestDecision order (ruleTied t.votes) = .eliminate e := by
  obtain ⟨-, -, hc⟩ := rule_eq_eliminate hr
  rcases hc with ⟨s, -, rfl⟩ | ⟨-, ⟨z, hz, rfl⟩ | ⟨hz, rfl⟩⟩
  · exact absurd rfl (hnb s)
  · rw [hz]
    rfl
  · exact lowestDecision_of_ne hz

theorem ruleCounty_winner {order : List Nat} {t : Tally} {w : Option Nat}
    (h : ruleCounty order t = .winner w) : t.votes.length ≤ 2 ∧ w = countyWinner t.votes := by
  unfold ruleCounty at h
  by_cases h2 : t.votes.length ≤ 2
  · rw [ite_eq_left h2] at h
    injection h with h
    exact ⟨h2, h.symm⟩
  · rw [ite_eq_right h2] at h
    exact absurd h lowestDecision_ne_winner

theorem ruleCounty_of_le {order : List Nat} {t : Tally} (h : t.votes.length ≤ 2) :
    ruleCounty order t = .winner (countyWinner t.votes) := by
  unfold ruleCounty
  rw [ite_eq_left h]

theorem ruleCounty_of_gt {order : List Nat} {t : Tally} (h : 2 < t.votes.length) :
    ruleCounty order t = lowestDecision order (ruleTied t.votes) := by
  unfold ruleCounty
  rw [ite_eq_right (by omega)]

theorem exists_ne {S : List Nat} (hS : S.Nodup) (h : 2 ≤ S.length) (z : Nat) :
    ∃ y ∈ S, y ≠ z := by
  match S, hS, h with
  | a :: b :: _, hS, _ =>
    have hab : a ≠ b := fun h => (List.nodup_cons.1 hS).1 (by simp [h])
    by_cases ha : a = z
    · exact ⟨b, by simp, fun h => hab (ha.trans h.symm)⟩
    · exact ⟨a, by simp, ha⟩

/-! ## The county count -/

/-- In the county count from a set without duplicates against which `w` holds a majority, `w`
continues in every round, and the county count names it. -/
theorem county_holder (hI : Closed interp) (hS : Stable interp) {order : List Nat} :
    ∀ {S : List Nat} {rds : List Round} {w0 : Option Nat},
      Trace interp (ruleCounty order) ballots S rds w0 → S.Nodup → ∀ {w : Nat}, w ∈ S →
        (tally interp S ballots).continuing < 2 * votesFor interp S ballots w →
        (∀ rd ∈ rds, w ∈ continuingSet rd) ∧ w0 = some w := by
  intro S rds w0 ht
  induction ht with
  | @last S w0 hr =>
    intro hSn w hw hm
    obtain ⟨hle, rfl⟩ := ruleCounty_winner hr
    refine ⟨by simp [continuingSet_tally, hw], ?_⟩
    rw [votes_length] at hle
    rw [continuing_eq_sum] at hm
    rw [votes_eq]
    clear hr
    match S, hSn, hw, hle, hm with
    | [], _, hw, _, _ => simp at hw
    | [a], _, hw, _, _ =>
      simp only [List.mem_singleton] at hw
      subst hw
      rfl
    | [a, b], _, hw, _, hm =>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      simp only [List.map_cons, List.map_nil, countyWinner]
      rcases hw with hw | hw <;> subst hw <;> split <;> (try split) <;>
        first | rfl | (exfalso; omega)
    | _ :: _ :: _ :: _, _, _, hle, _ => simp at hle
  | @step S e rds w0 hr hrest ih =>
    intro hSn w hw hm
    have hgt : 2 < (tally interp S ballots).votes.length := by
      by_cases h2 : (tally interp S ballots).votes.length ≤ 2
      · rw [ruleCounty_of_le h2] at hr
        cases hr
      · omega
    rw [ruleCounty_of_gt hgt] at hr
    obtain ⟨z, hzS, hez, hmin⟩ := lowest_min (List.ne_nil_of_mem hw) hr
    have hzw : z ≠ w := by
      intro hzw
      subst hzw
      rw [votes_length] at hgt
      obtain ⟨y, hyS, hyz⟩ := exists_ne hSn (by omega) z
      have := hmin y hyS
      have := two_le_continuing interp ballots hSn hw hyS (Ne.symm hyz)
      omega
    have hw1 : w ∈ S.filter fun i : Nat => decide (i ∉ e.eliminated) := by
      rw [hez]
      simp [hw, Ne.symm hzw]
    have hS1 : (S.filter fun i : Nat => decide (i ∉ e.eliminated)).Nodup :=
      List.filter_sublist.nodup hSn
    have hm1 := majority_subset hI hS hSn hS1 List.filter_sublist.subset ballots hw1 hm
    obtain ⟨h1, h2⟩ := ih hS1 hw1 hm1
    refine ⟨?_, h2⟩
    intro rd hrd
    rcases List.mem_cons.1 hrd with rfl | hrd
    · rw [continuingSet_tally]
      exact hw
    · exact h1 rd hrd

/-- The rounds of the count with two or more continuing candidates are rounds of the county count
from the same set, with the same counts, in the same order. -/
theorem county_rounds (hI : Closed interp) (hS : Stable interp) {order : List Nat} :
    ∀ {C : List Nat} {rds : List Round} {w : Option Nat},
      Trace interp (rule order) ballots C rds w → C.Nodup →
      ∀ {crds : List Round} {cw : Option Nat}, Trace interp (ruleCounty order) ballots C crds cw →
        ((rds.filter fun rd : Round => decide (2 ≤ (continuingSet rd).length)).map
          Round.tally).Sublist (crds.map Round.tally) := by
  intro C rds w ht
  induction ht with
  | @last C w hr =>
    intro _ crds cw hc
    obtain ⟨e0, crest, rfl⟩ := trace_cons hc
    rw [List.filter_cons]
    split <;> simp
  | @step C e rds w hr hrest ih =>
    intro hC crds cw hc
    have hC1 : (C.filter fun i : Nat => decide (i ∉ e.eliminated)).Nodup :=
      List.filter_sublist.nodup hC
    by_cases h3 : 2 < C.length
    · have hgt : 2 < (tally interp C ballots).votes.length := by
        rw [votes_length]
        exact h3
      have hcr := ruleCounty_of_gt (order := order) hgt
      have h2C : 2 ≤ C.length := by omega
      simp only [List.filter_cons, continuingSet_tally, decide_eq_true_eq, h2C, ↓reduceIte,
        List.map_cons]
      obtain ⟨e0, crest, hch⟩ := trace_cons hc
      by_cases hbat : ∃ B, e = .batch B
      · obtain ⟨B, rfl⟩ := hbat
        obtain ⟨X, hb⟩ := batchAt_of_rule hC hr
        have hc' : Trace interp (ruleCounty order) ballots
            (C.filter fun i : Nat => decide (i ∉ ([] : List Nat))) crds cw := by
          rw [filter_not_mem_nil]
          exact hc
        have hlen : (B.filter fun i : Nat => decide (i ∉ ([] : List Nat))).length = B.length := by
          rw [filter_not_mem_nil]
        rcases walk hb hI hS (fun _ _ h => ruleCounty_lowest h) B.length [] hlen (by simp) hc' with
          ⟨p, crds', h1, h2, h3, -⟩ | ⟨E', hE', ⟨b, hbB, hbE'⟩, hw, -⟩
        · have hsub := ih hC1 h2
          obtain ⟨r0, p', rfl⟩ : ∃ r0 p', p = r0 :: p' := by
            match p, h3 with
            | r0 :: p', _ => exact ⟨r0, p', rfl⟩
            | [], h3 => have := hb.two_le; simp at h3; omega
          have hr0 : r0.tally = tally interp C ballots := by
            rw [hch, List.cons_append, List.cons.injEq] at h1
            rw [← h1.1]
          rw [h1, List.cons_append, List.map_cons, hr0, List.map_append]
          exact (hsub.trans (List.sublist_append_right _ _)).cons_cons _
        · exfalso
          obtain ⟨hle, -⟩ := ruleCounty_winner hw
          rw [votes_length] at hle
          have hrest2 := hb.rest_two_le
          have hbD : b ∈ C.filter fun i : Nat => decide (i ∉ E') :=
            List.mem_filter.2 ⟨hb.sub hbB, by simp [hbE']⟩
          have heq : rest C B =
              (C.filter fun i : Nat => decide (i ∉ E')).filter fun i : Nat => decide (i ∉ B) := by
            rw [List.filter_filter]
            apply List.filter_congr
            intro x _
            by_cases hxB : x ∈ B
            · simp [hxB]
            · have hxE : x ∉ E' := fun h => hxB (hE' h)
              simp [hxB, hxE]
          have hlt : (rest C B).length < (C.filter fun i : Nat => decide (i ∉ E')).length := by
            rw [heq]
            exact List.length_filter_lt_length_iff_exists.2 ⟨b, hbD, by simp [hbB]⟩
          omega
      · have hnb : ∀ s, e ≠ .batch s := fun s h => hbat ⟨s, h⟩
        have hl := rule_lowest hr hnb
        rw [← hcr] at hl
        cases hc with
        | last h' =>
          rw [hl] at h'
          cases h'
        | step h' hcrest =>
          rename_i e' crest'
          rw [hl] at h'
          injection h' with h'
          subst h'
          exact (ih hC1 hcrest).cons_cons _
    · have hle : (tally interp C ballots).votes.length ≤ 2 := by
        rw [votes_length]
        omega
      obtain ⟨rfl, -⟩ := trace_unique hc (Trace.last (ruleCounty_of_le (order := order) hle))
      have hlt := eliminate_removes (rule_ends order) hr
      have hnil : (rds.filter fun rd : Round => decide (2 ≤ (continuingSet rd).length)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro rd hrd
        obtain ⟨-, hsub, -⟩ := hrest.mem rd hrd
        have := hsub.length_le
        simp only [decide_eq_true_eq]
        omega
      rw [List.filter_cons, hnil]
      split <;> simp

/-! ## The count's last rounds -/

/-- The count's winner holds a majority of the continuing ballots of its last round. -/
theorem trace_holder {order C : List Nat} {rds : List Round} {w : Option Nat} {w' : Nat}
    (ht : Trace interp (rule order) ballots C rds w) (hw : w = some w') :
    ∃ last v, rds.getLast? = some last ∧ (w', v) ∈ last.tally.votes ∧
      last.tally.continuing < 2 * v := by
  obtain ⟨last, hl, -, hr⟩ := ht.last_round
  rcases rule_eq_winner hr with ⟨x, hx, hm, hxw⟩ | ⟨-, hwn⟩
  · rw [hw] at hxw
    injection hxw with hxw
    subst hxw
    exact ⟨last, x.2, hl, hx, hm⟩
  · rw [hw] at hwn
    cases hwn

/-- When the count's last round, not its first, has one continuing candidate, the round before it
had two continuing candidates with equal votes. -/
theorem trace_tied {order C : List Nat}
    {rds : List Round} {w : Option Nat} (ht : Trace interp (rule order) ballots C rds w)
    (hC : C.Nodup) {p : List Round} {prev last : Round} (h : rds = p ++ [prev, last])
    (h1 : (continuingSet last).length = 1) :
    ∃ a b v, prev.tally.votes = [(a, v), (b, v)] := by
  have hsuf := trace_suffix p ht h
  obtain ⟨-, hsubC, -⟩ := ht.mem prev (by rw [h]; simp)
  have hSn : (continuingSet prev).Nodup := hsubC.nodup hC
  obtain ⟨e, hpe, hlast⟩ := hsuf.next 0 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpe hlast
  obtain ⟨htally, -, hrule⟩ := hsuf.mem prev (by simp)
  have hr : rule order (tally interp (continuingSet prev) ballots) = .eliminate e := by
    rw [← htally]
    exact hrule e hpe
  by_cases hbat : ∃ B, e = .batch B
  · obtain ⟨B, rfl⟩ := hbat
    obtain ⟨X, hb⟩ := batchAt_of_rule hSn hr
    have h3 : 2 ≤ (continuingSet last).length := by
      rw [hlast]
      exact hb.rest_two_le
    omega
  · have hnb : ∀ s, e ≠ .batch s := fun s h => hbat ⟨s, h⟩
    have h2 := two_le_of_eliminate (rule_ends order) hr
    obtain ⟨z, hzS, hez, -⟩ := lowest_min (S := continuingSet prev) (by
      intro hnil
      rw [hnil] at h2
      simp at h2) (rule_lowest hr hnb)
    have hlen : (continuingSet prev).length = 2 := by
      have heq : ((continuingSet prev).filter fun i : Nat => decide (i ∉ e.eliminated)) =
          (continuingSet prev).erase z := by
        rw [hSn.erase_eq_filter, hez]
        apply List.filter_congr
        intro x _
        by_cases hx : x = z <;> simp [hx]
      rw [hlast, heq, List.length_erase_of_mem hzS] at h1
      omega
    obtain ⟨-, hmaj, -⟩ := rule_eq_eliminate hr
    have hT := continuing_eq_sum interp (continuingSet prev) ballots
    rw [htally, votes_eq]
    match hS2 : continuingSet prev, hlen with
    | [a, b], _ =>
      rw [hS2] at hT hmaj
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hT
      have ha := hmaj (a, votesFor interp [a, b] ballots a) (mem_votes.2 ⟨by simp, rfl⟩)
      have hb := hmaj (b, votesFor interp [a, b] ballots b) (mem_votes.2 ⟨by simp, rfl⟩)
      simp only at ha hb
      refine ⟨a, b, votesFor interp [a, b] ballots a, ?_⟩
      simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
      omega

/-! ## T11 -/

/-- T11(a): if `w` holds a majority of the continuing ballots against the continuing set `S`, it
holds a majority against every continuing set `S'` with `w ∈ S' ⊆ S`. -/
theorem holder_subset (kinds : List Kind) (ballots : List (List UInt64)) {S S' : List Nat}
    (hS : S.Nodup) (hS' : S'.Nodup) (hsub : S' ⊆ S) {w : Nat} (hw : w ∈ S')
    (h : (tally (interpret kinds) S ballots).continuing <
      2 * votesFor (interpret kinds) S ballots w) :
    (tally (interpret kinds) S' ballots).continuing < 2 * votesFor (interpret kinds) S' ballots w :=
  majority_subset (interpret_closed kinds) (interpret_stable kinds) hS hS' hsub ballots hw h

theorem county_trace (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    Trace (interpret kinds) (ruleCounty order) ballots (countedSet kinds)
      (countyCount kinds order ballots).rounds (countyCount kinds order ballots).winner :=
  run_trace (ruleCounty_ends order) _ _ (by omega) (by omega)

/-- T11(b): a candidate that holds a majority in a round of the county count continues in every
later round of it, and the county count names it. -/
theorem county_majority (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {p q : List Round} {rd : Round} {w v : Nat}
    (h : (countyCount kinds order ballots).rounds = p ++ rd :: q) (hv : (w, v) ∈ rd.tally.votes)
    (hm : rd.tally.continuing < 2 * v) :
    (∀ rd' ∈ q, w ∈ continuingSet rd') ∧ (countyCount kinds order ballots).winner = some w := by
  have ht := county_trace kinds order ballots
  have hsuf := trace_suffix p ht h
  obtain ⟨htally, hsubC, -⟩ := ht.mem rd (by rw [h]; simp)
  have hSn := hsubC.nodup (countedSet_nodup kinds)
  rw [htally] at hv hm
  obtain ⟨hw, rfl⟩ := mem_votes.1 hv
  obtain ⟨h1, h2⟩ := county_holder (interpret_closed kinds) (interpret_stable kinds) hsuf hSn hw hm
  exact ⟨fun rd' hrd' => h1 rd' (List.mem_cons_of_mem rd hrd'), h2⟩

/-- T11(d): every round of the count with two or more continuing candidates is a round of the
county count with the same continuing set, votes, and inactive counts, in the same order. -/
theorem county_rounds_sublist (kinds : List Kind) (order : List Nat)
    (ballots : List (List UInt64)) :
    (((count kinds order ballots).rounds.filter fun rd : Round =>
        decide (2 ≤ (continuingSet rd).length)).map Round.tally).Sublist
      ((countyCount kinds order ballots).rounds.map Round.tally) :=
  county_rounds (interpret_closed kinds) (interpret_stable kinds) (count_trace kinds order ballots)
    (countedSet_nodup kinds) (county_trace kinds order ballots)

/-- A round of the count with two or more continuing candidates is a round of the county count. -/
theorem county_round_of_wide (kinds : List Kind) (order : List Nat)
    (ballots : List (List UInt64)) {rd : Round} (hrd : rd ∈ (count kinds order ballots).rounds)
    (h2 : 2 ≤ (continuingSet rd).length) :
    ∃ p q rdc, (countyCount kinds order ballots).rounds = p ++ rdc :: q ∧ rdc.tally = rd.tally := by
  have hmem : rd.tally ∈ (((count kinds order ballots).rounds.filter fun rd : Round =>
      decide (2 ≤ (continuingSet rd).length)).map Round.tally) :=
    List.mem_map_of_mem (List.mem_filter.2 ⟨hrd, by simpa using h2⟩)
  obtain ⟨rdc, hrdc, he⟩ := List.mem_map.1 ((county_rounds_sublist kinds order ballots).subset hmem)
  obtain ⟨p, q, hpq⟩ := List.append_of_mem hrdc
  exact ⟨p, q, rdc, hpq, he⟩

/-- T11(c), first statement: if the count names `w`, and its last round is round 1 or has two or
more continuing candidates, the county count names `w`. -/
theorem county_winner (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {w : Nat} (hw : (count kinds order ballots).winner = some w) {last : Round}
    (hl : (count kinds order ballots).rounds.getLast? = some last)
    (h : (count kinds order ballots).rounds.length = 1 ∨ 2 ≤ (continuingSet last).length) :
    (countyCount kinds order ballots).winner = some w := by
  have ht := count_trace kinds order ballots
  obtain ⟨last', v, hl', hv, hm⟩ := trace_holder ht hw
  rw [hl] at hl'
  injection hl' with hl'
  subst hl'
  rcases h with h1 | h2
  · obtain ⟨e0, rest, hcons⟩ := trace_cons ht
    have hrest : rest = [] := by
      rw [hcons, List.length_cons] at h1
      exact List.length_eq_zero_iff.1 (by omega)
    rw [hcons, hrest] at hl
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    rw [← hl] at hv hm
    obtain ⟨ce0, crest, hccons⟩ := trace_cons (county_trace kinds order ballots)
    exact (county_majority kinds order ballots (p := []) (q := crest) hccons hv hm).2
  · obtain ⟨p, q, rdc, hpq, he⟩ :=
      county_round_of_wide kinds order ballots (List.mem_of_getLast? hl) h2
    rw [← he] at hv hm
    exact (county_majority kinds order ballots hpq hv hm).2

/-- T11(c), second statement: if the count's last round has `w` alone and is not round 1, the
county count's last round has the continuing set and the counts of the count's round before it,
the tied round. -/
theorem county_tied (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64))
    {p : List Round} {prev last : Round} {w : Nat}
    (h : (count kinds order ballots).rounds = p ++ [prev, last])
    (hlast : continuingSet last = [w]) :
    ∃ rd, (countyCount kinds order ballots).rounds.getLast? = some rd ∧ rd.tally = prev.tally := by
  have ht := count_trace kinds order ballots
  obtain ⟨a, b, v, hab⟩ := trace_tied ht
    (countedSet_nodup kinds) h (by rw [hlast]; rfl)
  have h2 : (continuingSet prev).length = 2 := by
    simp [continuingSet, hab]
  obtain ⟨p', q', rdc, hpq, he⟩ :=
    county_round_of_wide kinds order ballots (rd := prev) (by rw [h]; simp) (by omega)
  have hc := county_trace kinds order ballots
  have hsuf := trace_suffix p' hc hpq
  obtain ⟨htally, -, -⟩ := hc.mem rdc (by rw [hpq]; simp)
  have hle : (tally (interpret kinds) (continuingSet rdc) ballots).votes.length ≤ 2 := by
    rw [votes_length]
    have : continuingSet rdc = continuingSet prev := by
      simp only [continuingSet, he]
    rw [this]
    omega
  obtain ⟨hq, -⟩ := trace_unique hsuf (Trace.last (ruleCounty_of_le (order := order) hle))
  rw [List.cons.injEq] at hq
  refine ⟨rdc, ?_, he⟩
  rw [hpq, hq.2, List.getLast?_concat]

end Demos.Rcv.Holder
