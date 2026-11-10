import Demos.Rcv.Spec

/-!
The theorems of the rounds of [the requirements](requirements.md), section "Theorems": T4
Elimination, T5 Conservation, T6 Locality, T7 Invariance, and T9 Order, over the count of
`Demos.Rcv.Spec`, with the general lemmas about `tally`, `rule`, and `run` that they rest on.

`Trace` describes the rounds of a count from a continuing set on: each round holds the counts of its
own continuing set, a round that `rule` ends is the last, and a round that eliminates is followed by
the rounds of its continuing set minus the eliminated candidates.  Every elimination removes at
least one member of the continuing set, and a set of at most one candidate ends the count, so
`run_trace` gives a `Trace` of `run` whenever the fuel is at least the larger of 1 and the size of
the set, and `Trace.run_eq` shows that every such fuel gives the same count.  The `K.length + 1`
rounds of `count` therefore suffice, as `count_trace` states.  The lemmas about `tally`, `rule`, and
`run` hold for every interpretation, which T10 needs.
-/

namespace Demos.Rcv.Rounds

open Demos.Rcv Demos.Rcv.Spec
open scoped List

/-! ## Lists -/

theorem sum_map_zero {α : Type} (l : List α) : (l.map fun _ : α => (0 : Nat)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map fun a : α => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_ite (C : List Nat) (j : Nat) :
    (C.map fun i : Nat => if j = i then 1 else 0).sum = C.count j := by
  induction C with
  | nil => rfl
  | cons i C ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.count_cons]
    by_cases h : j = i
    · subst h; simp; omega
    · have h' : (i == j) = false := by simp [Ne.symm h]
      simp [h, h']

theorem filter_sublist_filter {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = true → q a = true) → l.filter p <+ l.filter q
  | [], _ => List.Sublist.slnil
  | a :: l, h => by
    have ih := filter_sublist_filter (l := l) fun b hb => h b (List.mem_cons_of_mem a hb)
    rw [List.filter_cons, List.filter_cons]
    by_cases hp : p a = true
    · simp only [hp, h a List.mem_cons_self hp, ↓reduceIte]
      exact ih.cons_cons a
    · by_cases hq : q a = true
      · simp only [hp, hq, ↓reduceIte]
        exact ih.cons a
      · simp only [hp, hq]
        exact ih

/-- The last element of `order` that satisfies `p` comes after every other element of `order` that
satisfies it. -/
theorem getLast?_filter {order : List Nat} (hnd : order.Nodup) {p : Nat → Bool} {i : Nat}
    (h : (order.filter p).getLast? = some i) :
    i ∈ order ∧ p i = true ∧ ∀ j ∈ order, p j = true → order.idxOf j ≤ order.idxOf i := by
  induction order with
  | nil => simp at h
  | cons a rest ih =>
    have ha : a ∉ rest := (List.nodup_cons.1 hnd).1
    by_cases hf : rest.filter p = []
    · cases hpa : p a with
      | false => simp [hpa, hf] at h
      | true =>
        have hi : a = i := by simpa [List.filter_cons, hpa, hf] using h
        subst hi
        refine ⟨List.mem_cons_self, hpa, ?_⟩
        intro j hj hpj
        rcases List.mem_cons.1 hj with rfl | hj
        · exact Nat.le_refl _
        · exact absurd (List.mem_filter.2 ⟨hj, hpj⟩) (by simp [hf])
    · have h' : (rest.filter p).getLast? = some i := by
        obtain ⟨y, hy⟩ : ∃ y, (rest.filter p).getLast? = some y :=
          ⟨_, List.getLast?_eq_some_getLast hf⟩
        rw [List.filter_cons] at h
        split at h
        · rw [List.getLast?_cons, hy] at h
          rw [hy]
          simpa using h
        · exact h
      obtain ⟨hi, hpi, hle⟩ := ih (List.nodup_cons.1 hnd).2 h'
      have hai : (a == i) = false := by
        simp only [beq_eq_false_iff_ne]
        exact fun e => ha (e ▸ hi)
      refine ⟨List.mem_cons_of_mem a hi, hpi, ?_⟩
      intro j hj hpj
      rw [List.idxOf_cons, List.idxOf_cons, hai]
      by_cases hja : (a == j) = true
      · simp [hja]
      · rcases List.mem_cons.1 hj with rfl | hj
        · simp at hja
        · simp only [hja]
          have := hle j hj hpj
          simp only [Bool.false_eq_true, ↓reduceIte]
          omega

/-! ## The counted set -/

theorem countedSet_sublist (kinds : List Kind) : countedSet kinds <+ List.range' 1 kinds.length := by
  have h : ∀ l : List (Nat × Kind),
      (l.filterMap fun p : Nat × Kind => if countedKind p.2 then some p.1 else none) <+
        l.map Prod.fst := by
    intro l
    induction l with
    | nil => exact List.Sublist.slnil
    | cons p l ih =>
      by_cases hp : countedKind p.2 = true
      · simp only [List.filterMap_cons, hp, ↓reduceIte, List.map_cons]
        exact ih.cons_cons _
      · simp only [List.filterMap_cons, hp, List.map_cons]
        exact ih.cons _
  have hz : ((List.range' 1 kinds.length).zip kinds).map Prod.fst = List.range' 1 kinds.length :=
    List.map_fst_zip (by simp)
  unfold countedSet
  have := h ((List.range' 1 kinds.length).zip kinds)
  rwa [hz] at this

theorem countedSet_nodup (kinds : List Kind) : (countedSet kinds).Nodup :=
  (countedSet_sublist kinds).nodup List.nodup_range'

theorem mem_countedSet {kinds : List Kind} {i : Nat} (h : i ∈ countedSet kinds) :
    1 ≤ i ∧ i ≤ kinds.length := by
  have := List.mem_range'_1.1 ((countedSet_sublist kinds).subset h)
  omega

/-! ## Interpretation -/

theorem examine_counts {C : List Nat} {ps : List UInt64} {i : Nat}
    (h : examine C ps = some (.counts i)) : i ∈ C := by
  induction ps with
  | nil => simp [examine] at h
  | cons w ws ih =>
    unfold examine at h
    split at h
    · exact ih h
    · simp at h
    · split at h
      · simp only [Option.some.injEq, Outcome.counts.injEq] at h
        subst h
        assumption
      · exact ih h

/-- An interpretation by `interpret` counts a ballot only for a member of the continuing set. -/
theorem interpret_counts {kinds : List Kind} {C : List Nat} {ps : List UInt64} {i : Nat}
    (h : interpret kinds C ps = .counts i) : i ∈ C := by
  unfold interpret at h
  cases he : examine C ps with
  | none => simp [he] at h
  | some o =>
    simp only [he, Option.getD_some] at h
    subst h
    exact examine_counts he

/-! ## Tallies -/

/-- The continuing set of a round: the candidates of its votes, in their order. -/
def continuingSet (rd : Round) : List Nat := rd.tally.votes.map fun x : Nat × Nat => x.1

theorem tally_votes_fst (interp : List Nat → List UInt64 → Outcome) (C : List Nat)
    (ballots : List (List UInt64)) :
    (tally interp C ballots).votes.map (fun x : Nat × Nat => x.1) = C := by
  simp [tally, Function.comp_def]

@[simp] theorem continuingSet_tally (interp : List Nat → List UInt64 → Outcome) (C : List Nat)
    (ballots : List (List UInt64)) (e : Option Elimination) :
    continuingSet ⟨tally interp C ballots, e⟩ = C :=
  tally_votes_fst interp C ballots

/-- T5 for one round: when the continuing set has no repeated candidate and the interpretation
counts a ballot only for a member of it, the votes and the inactive counts sum to the number of
ballots. -/
theorem tally_sum (interp : List Nat → List UInt64 → Outcome) (C : List Nat)
    (ballots : List (List UInt64)) (hC : C.Nodup) (hi : ∀ ps i, interp C ps = .counts i → i ∈ C) :
    ((tally interp C ballots).votes.map fun x : Nat × Nat => x.2).sum +
        (tally interp C ballots).blank + (tally interp C ballots).uncounted +
        (tally interp C ballots).overvote + (tally interp C ballots).exhausted = ballots.length := by
  simp only [tally, List.map_map, Function.comp_def]
  induction ballots with
  | nil => simp [sum_map_zero]
  | cons ps ballots ih =>
    simp only [List.map_cons, List.count_cons, List.length_cons]
    rw [sum_map_add]
    cases h : interp C ps with
    | counts j =>
      have hs : (C.map fun i : Nat =>
          if (Outcome.counts j == Outcome.counts i) = true then 1 else 0).sum = 1 := by
        simp only [beq_iff_eq, Outcome.counts.injEq]
        rw [sum_map_ite, hC.count_of_mem (hi ps j h)]
      rw [hs]
      simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte]
      omega
    | inactive r =>
      have hs : (C.map fun i : Nat =>
          if (Outcome.inactive r == Outcome.counts i) = true then 1 else 0).sum = 0 := by
        simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte]
        exact sum_map_zero C
      rw [hs]
      cases r <;>
        simp only [beq_iff_eq, reduceCtorEq, Outcome.inactive.injEq, ↓reduceIte] <;> omega

/-! ## Rules -/

/-- The tied set of rule 4 as `rule` computes it. -/
def ruleTied (votes : List (Nat × Nat)) : List Nat :=
  (votes.filter fun x : Nat × Nat => x.2 = ((votes.map fun x : Nat × Nat => x.2).min?).getD 0).map
    fun x : Nat × Nat => x.1

/-- The candidates with the fewest votes, in the order of `votes`. -/
def fewest (votes : List (Nat × Nat)) : List Nat :=
  (votes.filter fun x : Nat × Nat => votes.all fun y : Nat × Nat => x.2 ≤ y.2).map
    fun x : Nat × Nat => x.1

theorem ruleTied_eq_fewest (votes : List (Nat × Nat)) : ruleTied votes = fewest votes := by
  unfold ruleTied fewest
  congr 1
  apply List.filter_congr
  intro x hx
  obtain ⟨m, hm⟩ : ∃ m, (votes.map fun x : Nat × Nat => x.2).min? = some m :=
    Option.isSome_iff_exists.1 (List.isSome_min?_of_mem (List.mem_map_of_mem hx))
  obtain ⟨hmem, hle⟩ := List.min?_eq_some_iff.1 hm
  rw [hm, Option.getD_some]
  obtain ⟨y, hy, hym⟩ := List.mem_map.1 hmem
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro hxm z hz
    rw [hxm]
    exact hle z.2 (List.mem_map_of_mem hz)
  · intro hall
    have h1 := hall y hy
    have h2 := hle x.2 (List.mem_map_of_mem hx)
    omega

theorem fewest_ne_nil {votes : List (Nat × Nat)} (h : votes ≠ []) : fewest votes ≠ [] := by
  rw [← ruleTied_eq_fewest]
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil votes h
  obtain ⟨m, hm⟩ : ∃ m, (votes.map fun x : Nat × Nat => x.2).min? = some m :=
    Option.isSome_iff_exists.1 (List.isSome_min?_of_mem (List.mem_map_of_mem hx))
  obtain ⟨hmem, -⟩ := List.min?_eq_some_iff.1 hm
  obtain ⟨y, hy, hym⟩ := List.mem_map.1 hmem
  unfold ruleTied
  rw [hm, Option.getD_some]
  intro hnil
  have : y.1 ∈ (votes.filter fun x : Nat × Nat => decide (x.2 = m)).map fun x : Nat × Nat => x.1 :=
    List.mem_map_of_mem (List.mem_filter.2 ⟨hy, by simpa using hym⟩)
  rw [hnil] at this
  simp at this

theorem fewest_sub {votes : List (Nat × Nat)} {i : Nat} (h : i ∈ fewest votes) :
    i ∈ votes.map fun x : Nat × Nat => x.1 := by
  unfold fewest at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  exact List.mem_map_of_mem (List.mem_filter.1 hx).1

/-- The step of `batch`'s fold keeps the first of the longest sets. -/
theorem foldl_longest {step : Option (List Nat) → List Nat → Option (List Nat)}
    (hnone : ∀ s, step none s = some s)
    (hsome : ∀ b s, step (some b) s = if b.length < s.length then some s else some b) :
    ∀ (sets : List (List Nat)) (init : Option (List Nat)) (r : List Nat),
      sets.foldl step init = some r →
        (init = some r ∨ r ∈ sets) ∧ (∀ b, init = some b → b.length ≤ r.length) ∧
          ∀ s ∈ sets, s.length ≤ r.length
  | [], init, r, h => by
    simp only [List.foldl_nil] at h
    subst h
    simp
  | s :: rest, init, r, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2, h3⟩ := foldl_longest hnone hsome rest _ r h
    cases init with
    | none =>
      rw [hnone] at h1 h2
      refine ⟨?_, by simp, ?_⟩
      · rcases h1 with h1 | h1
        · simp only [Option.some.injEq] at h1
          subst h1
          exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem s h1)
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h2 x rfl
        · exact h3 x hx
    | some b =>
      rw [hsome] at h1 h2
      by_cases hlt : b.length < s.length
      · simp only [hlt, ↓reduceIte, Option.some.injEq] at h1 h2
        have hs := h2 s rfl
        refine ⟨?_, ?_, ?_⟩
        · rcases h1 with h1 | h1
          · subst h1; exact Or.inr List.mem_cons_self
          · exact Or.inr (List.mem_cons_of_mem s h1)
        · intro x hx
          simp only [Option.some.injEq] at hx
          subst hx
          omega
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hs
          · exact h3 x hx
      · simp only [hlt, ↓reduceIte, Option.some.injEq] at h1 h2
        have hb := h2 b rfl
        refine ⟨?_, ?_, ?_⟩
        · rcases h1 with h1 | h1
          · exact Or.inl (congrArg some h1)
          · exact Or.inr (List.mem_cons_of_mem s h1)
        · intro x hx
          simp only [Option.some.injEq] at hx
          subst hx
          exact hb
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · omega
          · exact h3 x hx

theorem foldl_some {step : Option (List Nat) → List Nat → Option (List Nat)}
    (hsome : ∀ b s, step (some b) s = if b.length < s.length then some s else some b) :
    ∀ (sets : List (List Nat)) (b : List Nat), sets.foldl step (some b) ≠ none
  | [], _ => by simp
  | s :: rest, b => by
    simp only [List.foldl_cons, hsome]
    split
    · exact foldl_some hsome rest s
    · exact foldl_some hsome rest b

/-- Rule 3 finds a batch: the largest qualifying `L(X)`, with two or more candidates. -/
theorem batch_some {votes : List (Nat × Nat)} {s : List Nat} (h : batch votes = some s) :
    2 ≤ s.length ∧
      (∃ x ∈ votes, qualifies votes x = true ∧ s = (lower votes x.2).map fun y : Nat × Nat => y.1) ∧
      ∀ y ∈ votes, qualifies votes y = true → ∀ z ∈ lower votes y.2, z.1 ∈ s := by
  unfold batch at h
  obtain ⟨hmem, -, hmax⟩ := foldl_longest (fun _ => rfl) (fun _ _ => rfl) _ _ _ h
  have hs := hmem.resolve_left (by simp)
  simp only [List.mem_filter, List.mem_map, decide_eq_true_eq] at hs
  obtain ⟨⟨x, ⟨hx, hqx⟩, rfl⟩, hlen⟩ := hs
  refine ⟨hlen, ⟨x, hx, hqx, rfl⟩, ?_⟩
  intro y hy hqy z hz
  have hzl := List.mem_filter.1 hz
  simp only [decide_eq_true_eq] at hzl
  apply List.mem_map_of_mem
  by_cases hyx : y.2 ≤ x.2
  · exact List.mem_filter.2 ⟨hzl.1, by simp; omega⟩
  · have hsub : lower votes x.2 <+ lower votes y.2 :=
      filter_sublist_filter fun a _ ha => by simp at ha ⊢; omega
    have hle : (lower votes y.2).length ≤ (lower votes x.2).length := by
      by_cases h2 : 2 ≤ (lower votes y.2).length
      · have := hmax ((lower votes y.2).map fun y : Nat × Nat => y.1) (by
          simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
          exact ⟨⟨y, ⟨hy, hqy⟩, rfl⟩, by simpa using h2⟩)
        simpa using this
      · simp only [List.length_map] at hlen
        omega
    rw [hsub.eq_of_length_le hle]
    exact hz

/-- Rule 3 finds no batch only when no qualifying `L(X)` has two or more candidates. -/
theorem batch_none {votes : List (Nat × Nat)} (h : batch votes = none) :
    ∀ y ∈ votes, qualifies votes y = true → (lower votes y.2).length < 2 := by
  unfold batch at h
  have hnil : ((votes.filter (qualifies votes)).map fun x : Nat × Nat =>
      (lower votes x.2).map fun y : Nat × Nat => y.1).filter
        (fun s : List Nat => 2 ≤ s.length) = [] := by
    revert h
    cases ((votes.filter (qualifies votes)).map fun x : Nat × Nat =>
      (lower votes x.2).map fun y : Nat × Nat => y.1).filter
        (fun s : List Nat => 2 ≤ s.length) with
    | nil => intro; rfl
    | cons s rest =>
      intro h
      exact absurd h (foldl_some (fun _ _ => rfl) rest s)
  intro y hy hq
  rw [List.filter_eq_nil_iff] at hnil
  have := hnil ((lower votes y.2).map fun z : Nat × Nat => z.1)
    (List.mem_map.2 ⟨y, List.mem_filter.2 ⟨hy, hq⟩, rfl⟩)
  simpa using this

/-- The member of a nonempty `Z` that `latest` returns belongs to `Z`, whatever the order. -/
theorem latest_mem {order Z : List Nat} (hne : Z ≠ []) : latest order Z ∈ Z := by
  unfold latest
  rw [List.getLastD_eq_getLast?]
  cases h : (order.filter fun i : Nat => decide (i ∈ Z)).getLast? with
  | none =>
    cases Z with
    | nil => exact absurd rfl hne
    | cons z Z => simp
  | some i =>
    simpa using (List.mem_filter.1 (List.mem_of_getLast? h)).2

theorem idxOf_inj {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l)
    (h : l.idxOf a = l.idxOf b) : a = b := by
  have g1 : l[l.idxOf a]? = some a := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem ha), List.getElem_idxOf]
  have g2 : l[l.idxOf b]? = some b := by
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hb), List.getElem_idxOf]
  rw [h, g2] at g1
  exact (Option.some.inj g1).symm

/-- When the order holds each member of `Z` once, `latest` returns the member of `Z` latest in the
order. -/
theorem latest_spec {order Z : List Nat} (hnd : order.Nodup) (hsub : ∀ j ∈ Z, j ∈ order)
    (hne : Z ≠ []) :
    latest order Z ∈ Z ∧ ∀ j ∈ Z, j ∈ order ∧ order.idxOf j ≤ order.idxOf (latest order Z) := by
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil Z hne
  have hf : (order.filter fun i : Nat => decide (i ∈ Z)) ≠ [] := by
    intro hnil
    have hmem : z ∈ order.filter fun i : Nat => decide (i ∈ Z) :=
      List.mem_filter.2 ⟨hsub z hz, by simpa using hz⟩
    rw [hnil] at hmem
    simp at hmem
  have hl := List.getLast?_eq_some_getLast hf
  obtain ⟨-, hpi, hle⟩ := getLast?_filter hnd hl
  have hlat : latest order Z = (order.filter fun i : Nat => decide (i ∈ Z)).getLast hf := by
    unfold latest
    rw [List.getLastD_eq_getLast?, hl, Option.getD_some]
  rw [hlat]
  refine ⟨by simpa using hpi, fun j hj => ⟨hsub j hj, hle j (hsub j hj) (by simpa using hj)⟩⟩

/-- The decision of rule 4 for the set `Z` of the candidates with the fewest votes. -/
def lowestDecision (order Z : List Nat) : Decision :=
  match Z with
  | [z] => .eliminate (.lowest z)
  | _ => .eliminate (.order Z (latest order Z))

theorem lowestDecision_of_ne {order Z : List Nat} (hz : ∀ z, Z ≠ [z]) :
    lowestDecision order Z = .eliminate (.order Z (latest order Z)) := by
  match Z, hz with
  | [], _ => rfl
  | [z], hz => exact absurd rfl (hz z)
  | _ :: _ :: _, _ => rfl

section Evaluation

variable {order : List Nat} {t : Tally}

theorem rule_of_majority {x : Nat × Nat}
    (hx : t.votes.find? (fun x : Nat × Nat => t.continuing < 2 * x.2) = some x) :
    rule order t = .winner (some x.1) := by
  unfold rule
  rw [hx]

theorem rule_of_zero (hx : t.votes.find? (fun x : Nat × Nat => t.continuing < 2 * x.2) = none)
    (h0 : t.continuing = 0) : rule order t = .winner none := by
  unfold rule
  rw [hx]
  simp only [h0, ↓reduceIte]

theorem rule_of_batch {s : List Nat}
    (hx : t.votes.find? (fun x : Nat × Nat => t.continuing < 2 * x.2) = none)
    (h0 : t.continuing ≠ 0) (hb : batch t.votes = some s) :
    rule order t = .eliminate (.batch s) := by
  unfold rule
  rw [hx, hb]
  simp only [h0, ↓reduceIte]

theorem rule_of_lowest
    (hx : t.votes.find? (fun x : Nat × Nat => t.continuing < 2 * x.2) = none)
    (h0 : t.continuing ≠ 0) (hb : batch t.votes = none) :
    rule order t = lowestDecision order (ruleTied t.votes) := by
  unfold rule
  rw [hx, hb]
  simp only [h0, ↓reduceIte] <;> rfl

end Evaluation

theorem rule_eq_winner {order : List Nat} {t : Tally} {w : Option Nat}
    (h : rule order t = .winner w) :
    (∃ x ∈ t.votes, t.continuing < 2 * x.2 ∧ w = some x.1) ∨ (t.continuing = 0 ∧ w = none) := by
  cases hx : t.votes.find? (fun x : Nat × Nat => t.continuing < 2 * x.2) with
  | some x =>
    rw [rule_of_majority hx] at h
    cases h
    exact Or.inl ⟨x, List.mem_of_find?_eq_some hx, by simpa using List.find?_some hx, rfl⟩
  | none =>
    by_cases h0 : t.continuing = 0
    · rw [rule_of_zero hx h0] at h
      cases h
      exact Or.inr ⟨h0, rfl⟩
    · cases hb : batch t.votes with
      | some s =>
        rw [rule_of_batch hx h0 hb] at h
        cases h
      | none =>
        rw [rule_of_lowest hx h0 hb] at h
        unfold lowestDecision at h
        split at h <;> cases h

/-- The decision of a round that eliminates, by the rules of `rule`. -/
theorem rule_eq_eliminate {order : List Nat} {t : Tally} {e : Elimination}
    (h : rule order t = .eliminate e) :
    0 < t.continuing ∧ (∀ x ∈ t.votes, 2 * x.2 ≤ t.continuing) ∧
      ((∃ s, batch t.votes = some s ∧ e = .batch s) ∨
        (batch t.votes = none ∧
          ((∃ z, ruleTied t.votes = [z] ∧ e = .lowest z) ∨
            ((∀ z, ruleTied t.votes ≠ [z]) ∧
              e = .order (ruleTied t.votes) (latest order (ruleTied t.votes)))))) := by
  cases hx : t.votes.find? (fun x : Nat × Nat => t.continuing < 2 * x.2) with
  | some x =>
    rw [rule_of_majority hx] at h
    cases h
  | none =>
    have hmaj : ∀ x ∈ t.votes, 2 * x.2 ≤ t.continuing := by
      intro x hxm
      have := List.find?_eq_none.1 hx x hxm
      simp only [decide_eq_true_eq] at this
      omega
    by_cases h0 : t.continuing = 0
    · rw [rule_of_zero hx h0] at h
      cases h
    · refine ⟨Nat.pos_of_ne_zero h0, hmaj, ?_⟩
      cases hb : batch t.votes with
      | some s =>
        rw [rule_of_batch hx h0 hb] at h
        cases h
        exact Or.inl ⟨s, rfl, rfl⟩
      | none =>
        rw [rule_of_lowest hx h0 hb] at h
        refine Or.inr ⟨rfl, ?_⟩
        by_cases hz : ∃ z, ruleTied t.votes = [z]
        · obtain ⟨z, hz⟩ := hz
          rw [hz] at h
          simp only [lowestDecision, Decision.eliminate.injEq] at h
          exact Or.inl ⟨z, hz, h.symm⟩
        · have hz' : ∀ z, ruleTied t.votes ≠ [z] := fun z h' => hz ⟨z, h'⟩
          rw [lowestDecision_of_ne hz'] at h
          cases h
          exact Or.inr ⟨hz', rfl⟩

theorem votes_ne_nil {t : Tally} (h : 0 < t.continuing) : t.votes ≠ [] := by
  intro hnil
  simp [Tally.continuing, hnil] at h

/-- The candidates that a round eliminates are members of its continuing set, at least one. -/
theorem rule_eliminated {order : List Nat} {t : Tally} {e : Elimination}
    (h : rule order t = .eliminate e) :
    e.eliminated ≠ [] ∧ ∀ i ∈ e.eliminated, i ∈ t.votes.map fun x : Nat × Nat => x.1 := by
  obtain ⟨hpos, -, hcases⟩ := rule_eq_eliminate h
  rcases hcases with ⟨s, hs, rfl⟩ | ⟨-, ⟨z, hz, rfl⟩ | ⟨-, rfl⟩⟩
  · obtain ⟨hlen, ⟨x, -, -, rfl⟩, -⟩ := batch_some hs
    refine ⟨fun hnil => by simp [Elimination.eliminated] at hnil; simp [hnil] at hlen, ?_⟩
    intro i hi
    simp only [Elimination.eliminated, List.mem_map] at hi
    obtain ⟨y, hy, rfl⟩ := hi
    exact List.mem_map_of_mem (List.mem_filter.1 hy).1
  · refine ⟨by simp [Elimination.eliminated], ?_⟩
    intro i hi
    simp only [Elimination.eliminated, List.mem_singleton] at hi
    subst hi
    rw [ruleTied_eq_fewest] at hz
    exact fewest_sub (by rw [hz]; exact List.mem_singleton_self _)
  · have hne : ruleTied t.votes ≠ [] := by
      rw [ruleTied_eq_fewest]
      exact fewest_ne_nil (votes_ne_nil hpos)
    refine ⟨by simp [Elimination.eliminated], ?_⟩
    intro i hi
    simp only [Elimination.eliminated, List.mem_singleton] at hi
    subst hi
    have := latest_mem (order := order) hne
    rw [ruleTied_eq_fewest] at this ⊢
    exact fewest_sub this

/-- Each round that eliminates removes at least one member of its continuing set. -/
theorem rule_eliminate_removes {interp : List Nat → List UInt64 → Outcome} {order C : List Nat}
    {ballots : List (List UInt64)} {e : Elimination}
    (h : rule order (tally interp C ballots) = .eliminate e) :
    (C.filter fun i : Nat => decide (i ∉ e.eliminated)).length < C.length := by
  obtain ⟨hne, hsub⟩ := rule_eliminated h
  rw [tally_votes_fst] at hsub
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hne
  exact List.length_filter_lt_length_iff_exists.2 ⟨i, hsub i hi, by simp [hi]⟩

/-- A round whose continuing set has at most one member ends the count, by rule 1 or rule 2. -/
theorem rule_winner_of_length_le_one (order : List Nat) (t : Tally) (h : t.votes.length ≤ 1) :
    ∃ w, rule order t = .winner w := by
  match hv : t.votes, h with
  | [], _ => exact ⟨none, by simp [rule, Tally.continuing, hv]⟩
  | [x], _ =>
    by_cases hx : x.2 = 0
    · exact ⟨none, by simp [rule, Tally.continuing, hv, hx]⟩
    · have : x.2 < 2 * x.2 := by omega
      exact ⟨some x.1, by simp [rule, Tally.continuing, hv, this]⟩

/-- The requirements' description of an elimination `e` in a round with the counts `t` and the
tie-break order `order`, from T4: `Tᵣ > 0`, no candidate holds a majority, and the elimination is
(a) a batch of two or more candidates that is `L(X)` for a qualifying `X` and holds every
qualifying `L(Y)`; or, when no qualifying `L(Y)` has two or more candidates, (b) the candidate with
the fewest votes when it alone has them, or (c) the set of the two or more candidates with the
fewest votes, marked as tied, and the member of it latest in the order. -/
def Eliminates (order : List Nat) (t : Tally) (e : Elimination) : Prop :=
  0 < t.continuing ∧ (∀ x ∈ t.votes, 2 * x.2 ≤ t.continuing) ∧
    ((∃ s : List Nat, e = .batch s ∧ 2 ≤ s.length ∧
        (∃ x ∈ t.votes, qualifies t.votes x = true ∧
          s = (lower t.votes x.2).map fun y : Nat × Nat => y.1) ∧
        ∀ y ∈ t.votes, qualifies t.votes y = true → ∀ z ∈ lower t.votes y.2, z.1 ∈ s) ∨
      ((∀ y ∈ t.votes, qualifies t.votes y = true → (lower t.votes y.2).length < 2) ∧
        ((∃ z : Nat, fewest t.votes = [z] ∧ e = .lowest z) ∨
          (2 ≤ (fewest t.votes).length ∧ ∃ i ∈ fewest t.votes, e = .order (fewest t.votes) i ∧
            ∀ j ∈ fewest t.votes, j ∈ order ∧ order.idxOf j ≤ order.idxOf i))))

/-- `rule`'s eliminations meet the requirements' description when the order holds each candidate
of the round once. -/
theorem rule_eliminates {order : List Nat} {t : Tally} {e : Elimination}
    (h : rule order t = .eliminate e) (hnd : order.Nodup) (hord : ∀ x ∈ t.votes, x.1 ∈ order) :
    Eliminates order t e := by
  obtain ⟨hpos, hmaj, hcases⟩ := rule_eq_eliminate h
  refine ⟨hpos, hmaj, ?_⟩
  rcases hcases with ⟨s, hs, rfl⟩ | ⟨hb, hcases⟩
  · exact Or.inl ⟨s, rfl, batch_some hs⟩
  · refine Or.inr ⟨batch_none hb, ?_⟩
    rw [ruleTied_eq_fewest] at hcases
    rcases hcases with ⟨z, hz, rfl⟩ | ⟨hz, rfl⟩
    · exact Or.inl ⟨z, hz, rfl⟩
    · have hne := fewest_ne_nil (votes_ne_nil hpos)
      have hsub : ∀ j ∈ fewest t.votes, j ∈ order := by
        intro j hj
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (fewest_sub hj)
        exact hord x hx
      obtain ⟨hmem, hlast⟩ := latest_spec hnd hsub hne
      refine Or.inr ⟨?_, _, hmem, rfl, hlast⟩
      match hf : fewest t.votes, hne, hz with
      | [], hne, _ => exact absurd rfl hne
      | [z], _, hz => exact absurd rfl (hz z)
      | _ :: _ :: _, _, _ => simp

/-- `rule` under the order `π'` decides as under `π` when, in case of an elimination by order
under `π`, `π'` chooses the same member of the tied set. -/
theorem rule_order {π π' : List Nat} {t : Tally}
    (h : ∀ Z i, rule π t = .eliminate (.order Z i) → latest π' Z = i) : rule π' t = rule π t := by
  cases hx : t.votes.find? (fun x : Nat × Nat => t.continuing < 2 * x.2) with
  | some x => rw [rule_of_majority hx, rule_of_majority hx]
  | none =>
    by_cases h0 : t.continuing = 0
    · rw [rule_of_zero hx h0, rule_of_zero hx h0]
    · cases hb : batch t.votes with
      | some s => rw [rule_of_batch hx h0 hb, rule_of_batch hx h0 hb]
      | none =>
        rw [rule_of_lowest hx h0 hb, rule_of_lowest hx h0 hb]
        by_cases hz : ∃ z, ruleTied t.votes = [z]
        · obtain ⟨z, hz⟩ := hz
          rw [hz]
          rfl
        · have hz' : ∀ z, ruleTied t.votes ≠ [z] := fun z h' => hz ⟨z, h'⟩
          rw [lowestDecision_of_ne hz', lowestDecision_of_ne hz',
            h _ _ (by rw [rule_of_lowest hx h0 hb, lowestDecision_of_ne hz'])]

/-! ## Rounds -/

/-- The rounds `rds` and the winner `w` of a count under the interpretation `interp`, the tie-break
order `order`, and the ballots `ballots`, from the continuing set `C` on.  Each round holds the
counts of its continuing set; a round that `rule` ends is the last, with no elimination, and a round
that eliminates is followed by the rounds from its continuing set minus the eliminated
candidates. -/
inductive Trace (interp : List Nat → List UInt64 → Outcome) (order : List Nat)
    (ballots : List (List UInt64)) : List Nat → List Round → Option Nat → Prop
  | last {C : List Nat} {w : Option Nat} :
    rule order (tally interp C ballots) = .winner w →
      Trace interp order ballots C [⟨tally interp C ballots, none⟩] w
  | step {C : List Nat} {e : Elimination} {rds : List Round} {w : Option Nat} :
    rule order (tally interp C ballots) = .eliminate e →
      Trace interp order ballots (C.filter fun i : Nat => decide (i ∉ e.eliminated)) rds w →
        Trace interp order ballots C (⟨tally interp C ballots, some e⟩ :: rds) w

variable {interp : List Nat → List UInt64 → Outcome} {order : List Nat}
  {ballots : List (List UInt64)}

/-- A round that eliminates has two or more continuing candidates. -/
theorem two_le_of_eliminate {C : List Nat} {e : Elimination}
    (hr : rule order (tally interp C ballots) = .eliminate e) : 2 ≤ C.length := by
  apply Nat.le_of_not_lt
  intro hc
  obtain ⟨w', hw'⟩ := rule_winner_of_length_le_one order (tally interp C ballots)
    (by simp [tally]; omega)
  rw [hr] at hw'
  cases hw'

/-- A count has at most the larger of 1 and the size of its first continuing set rounds. -/
theorem Trace.length_le {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace interp order ballots C rds w) : rds.length ≤ max 1 C.length := by
  induction h with
  | last => exact Nat.le_max_left 1 _
  | @step C e rds w hr _ ih =>
    have hlt := rule_eliminate_removes hr
    have h2 := two_le_of_eliminate hr
    simp only [List.length_cons]
    omega

/-- `run` gives the trace of the count whenever the fuel is at least the larger of 1 and the size
of the continuing set. -/
theorem run_trace :
    ∀ (fuel : Nat) (C : List Nat), 1 ≤ fuel → C.length ≤ fuel →
      Trace interp order ballots C (run interp order ballots fuel C).rounds
        (run interp order ballots fuel C).winner
  | 0, _, h1, _ => absurd h1 (by decide)
  | fuel + 1, C, _, hC => by
    cases hr : rule order (tally interp C ballots) with
    | winner w =>
      simp only [run, hr]
      exact Trace.last hr
    | eliminate e =>
      simp only [run, hr]
      have hlt := rule_eliminate_removes hr
      have h2 := two_le_of_eliminate hr
      exact Trace.step hr (run_trace fuel _ (by omega) (by omega))

/-- Every fuel at least the length of a trace gives the trace's count. -/
theorem Trace.run_eq {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace interp order ballots C rds w) :
    ∀ fuel, rds.length ≤ fuel → run interp order ballots fuel C = ⟨rds, w⟩ := by
  induction h with
  | @last C w hr =>
    intro fuel hf
    match fuel, hf with
    | fuel + 1, _ => simp [run, hr]
  | @step C e rds w hr _ ih =>
    intro fuel hf
    match fuel, hf with
    | fuel + 1, hf =>
      simp only [List.length_cons] at hf
      simp only [run, hr]
      rw [ih fuel (by omega)]

/-- The fuel does not change the count once it is at least the larger of 1 and the size of the
continuing set. -/
theorem run_fuel {C : List Nat} {fuel fuel' : Nat} (h : max 1 C.length ≤ fuel)
    (h' : max 1 C.length ≤ fuel') :
    run interp order ballots fuel C = run interp order ballots fuel' C := by
  have ht := run_trace (interp := interp) (order := order) (ballots := ballots) fuel C
    (by omega) (by omega)
  have hl := ht.length_le
  rw [ht.run_eq fuel (by omega), ht.run_eq fuel' (by omega)]

/-- The rounds of `count` form a trace from the counted set: the `K.length + 1` rounds that `run`
allows suffice. -/
theorem count_trace (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    Trace (interpret kinds) order ballots (countedSet kinds) (count kinds order ballots).rounds
      (count kinds order ballots).winner :=
  run_trace _ _ (by omega) (by omega)

/-- Each round of a trace holds the counts of its continuing set, a subset of the first one, and
its elimination is the decision of `rule`. -/
theorem Trace.mem {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace interp order ballots C rds w) :
    ∀ rd ∈ rds, rd.tally = tally interp (continuingSet rd) ballots ∧ continuingSet rd <+ C ∧
      ∀ e, rd.elimination = some e → rule order rd.tally = .eliminate e := by
  induction h with
  | @last C w hr =>
    intro rd hrd
    simp only [List.mem_singleton] at hrd
    subst hrd
    simp
  | @step C e rds w hr _ ih =>
    intro rd hrd
    rcases List.mem_cons.1 hrd with rfl | hrd
    · simp only [continuingSet_tally, List.Sublist.refl, Option.some.injEq, true_and]
      intro e' he'
      rw [← he']
      exact hr
    · obtain ⟨h1, h2, h3⟩ := ih rd hrd
      exact ⟨h1, h2.trans List.filter_sublist, h3⟩

/-- The first round of a trace from `C` has the continuing set `C`. -/
theorem Trace.head {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace interp order ballots C rds w) :
    ∃ hr : 0 < rds.length, continuingSet rds[0] = C := by
  cases h with
  | last => exact ⟨by simp, by simp⟩
  | step => exact ⟨by simp, by simp⟩

/-- Each round of a trace but the last eliminates, and the next round's continuing set is its own
minus the eliminated candidates. -/
theorem Trace.next {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace interp order ballots C rds w) :
    ∀ (r : Nat) (hr : r + 1 < rds.length), ∃ e, rds[r].elimination = some e ∧
      continuingSet rds[r + 1] =
        (continuingSet rds[r]).filter fun i : Nat => decide (i ∉ e.eliminated) := by
  induction h with
  | last => intro r hr; simp at hr
  | @step C e rds w hr ht ih =>
    intro r hr'
    cases r with
    | zero =>
      obtain ⟨h0, hc⟩ := ht.head
      refine ⟨e, rfl, ?_⟩
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, continuingSet_tally]
      exact hc
    | succ r =>
      simp only [List.getElem_cons_succ]
      exact ih r (by simp only [List.length_cons] at hr'; omega)

/-- The last round of a trace eliminates no one, and `rule` ends the count with its winner. -/
theorem Trace.last_round {C : List Nat} {rds : List Round} {w : Option Nat}
    (h : Trace interp order ballots C rds w) :
    ∃ last, rds.getLast? = some last ∧ last.elimination = none ∧ rule order last.tally = .winner w := by
  induction h with
  | @last C w hr => exact ⟨_, rfl, rfl, hr⟩
  | @step C e rds w hr ht ih =>
    obtain ⟨last, hl, he, hw⟩ := ih
    refine ⟨last, ?_, he, hw⟩
    rw [List.getLast?_cons, hl]
    rfl

/-- The count does not depend on the order of the ballots. -/
theorem tally_perm {C : List Nat} {ballots' : List (List UInt64)} (h : ballots'.Perm ballots) :
    tally interp C ballots' = tally interp C ballots := by
  simp only [tally, (h.map (interp C)).count_eq]

theorem run_perm {ballots' : List (List UInt64)} (h : ballots'.Perm ballots) :
    ∀ (fuel : Nat) (C : List Nat),
      run interp order ballots' fuel C = run interp order ballots fuel C
  | 0, _ => rfl
  | fuel + 1, C => by
    simp only [run, tally_perm h, run_perm h fuel]

/-- The count under the order `π'` equals the count under `π` when `π'` chooses, at each round of
the count under `π` that eliminates by order, the same member of the tied set. -/
theorem run_order {π π' : List Nat} :
    ∀ (fuel : Nat) (C : List Nat),
      (∀ rd ∈ (run interp π ballots fuel C).rounds, ∀ Z i,
        rd.elimination = some (.order Z i) → latest π' Z = i) →
      run interp π' ballots fuel C = run interp π ballots fuel C
  | 0, _, _ => rfl
  | fuel + 1, C, h => by
    have hrule : rule π' (tally interp C ballots) = rule π (tally interp C ballots) := by
      apply rule_order
      intro Z i hr
      have := h ⟨tally interp C ballots, some (.order Z i)⟩ (by simp [run, hr])
      exact this Z i rfl
    cases hr : rule π (tally interp C ballots) with
    | winner w => simp [run, hr, hrule]
    | eliminate e =>
      have hrest := run_order (π := π) (π' := π') fuel
        (C.filter fun i : Nat => decide (i ∉ e.eliminated)) (by
          intro rd hrd
          apply h rd
          simp only [run, hr, List.mem_cons]
          exact Or.inr hrd)
      simp only [run, hr, hrule, hrest]

/-! ## The theorems -/

/-- T4 Elimination.  In every round that eliminates, `Tᵣ > 0`, no candidate holds a majority, and
the elimination is a batch, a lowest elimination, or an elimination by order as `Eliminates`
states.  The last round eliminates no one and ends by rule 1, with the candidate that holds a
majority as the winner, or by rule 2, with `Tᵣ = 0` and no winner. -/
theorem elimination (c : Contest) (hc : c.WellFormed) :
    (∀ rd ∈ (countContest c).rounds, ∀ e : Elimination, rd.elimination = some e →
      Eliminates c.order rd.tally e) ∧
    ∃ last : Round, (countContest c).rounds.getLast? = some last ∧ last.elimination = none ∧
      ((∃ x ∈ last.tally.votes, last.tally.continuing < 2 * x.2 ∧
          (countContest c).winner = some x.1) ∨
        (last.tally.continuing = 0 ∧ (countContest c).winner = none)) := by
  have ht := count_trace (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)
  have hperm := hc.2.2.2.2.2.2.2.1
  have hnd : c.order.Nodup := hperm.nodup_iff.2 List.nodup_range'
  refine ⟨?_, ?_⟩
  · intro rd hrd e he
    obtain ⟨-, hsub, hrule⟩ := ht.mem rd hrd
    apply rule_eliminates (hrule e he) hnd
    intro x hx
    have hxC : x.1 ∈ continuingSet rd := List.mem_map_of_mem hx
    have hb := mem_countedSet (hsub.subset hxC)
    apply hperm.mem_iff.2
    simp only [kindsOf, List.length_map] at hb
    exact List.mem_range'_1.2 ⟨hb.1, by omega⟩
  · obtain ⟨last, hl, he, hw⟩ := ht.last_round
    exact ⟨last, hl, he, rule_eq_winner hw⟩

/-- T5 Conservation.  In every round, the votes of the continuing candidates and the inactive
counts by reason sum to the number of ballots, and `continuing` is the sum of the votes. -/
theorem conservation (c : Contest) :
    ∀ rd ∈ (countContest c).rounds,
      (rd.tally.votes.map fun x : Nat × Nat => x.2).sum + rd.tally.blank + rd.tally.uncounted +
          rd.tally.overvote + rd.tally.exhausted = c.ballots.length ∧
        rd.tally.continuing = (rd.tally.votes.map fun x : Nat × Nat => x.2).sum := by
  intro rd hrd
  have ht := count_trace (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)
  obtain ⟨htally, hsub, -⟩ := ht.mem rd hrd
  refine ⟨?_, rfl⟩
  rw [htally]
  have := tally_sum (interpret (kindsOf c)) (continuingSet rd)
    (c.ballots.map fun b : Ballot => b.positions) (hsub.nodup (countedSet_nodup _))
    (fun _ _ h => interpret_counts h)
  rw [List.length_map] at this
  exact this

/-- T6 Locality.  Round 1 has the counted set as its continuing set.  In every round `r`, the votes
of each continuing candidate `i` are the number of ballots whose interpretation against `Cᵣ` counts
for `i`, each inactive count is the number of ballots whose interpretation against `Cᵣ` is inactive
with its reason, and every round but the last eliminates, with `Cᵣ₊₁` equal to `Cᵣ` minus the
eliminated candidates. -/
theorem locality (c : Contest) :
    let k := countContest c
    let ballots := c.ballots.map fun b : Ballot => b.positions
    (∃ h : 0 < k.rounds.length, continuingSet k.rounds[0] = countedSet (kindsOf c)) ∧
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
    ∀ (r : Nat) (h : r + 1 < k.rounds.length), ∃ e : Elimination,
      k.rounds[r].elimination = some e ∧
        continuingSet k.rounds[r + 1] =
          (continuingSet k.rounds[r]).filter fun i : Nat => decide (i ∉ e.eliminated) := by
  intro k ballots
  have ht : Trace (interpret (kindsOf c)) c.order ballots (countedSet (kindsOf c)) k.rounds
      k.winner := count_trace (kindsOf c) c.order ballots
  refine ⟨ht.head, ?_, ht.next⟩
  intro r hr C
  obtain ⟨htally, -, -⟩ := ht.mem k.rounds[r] (List.getElem_mem hr)
  rw [htally]
  simp only [tally, List.count_eq_countP, List.countP_map, Function.comp_def]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- T7 Invariance, over contest structures.  Replacing the ballots by ballots whose position words
are a permutation of theirs, which covers a permutation of the ballots and a change of their
identifiers, added, removed, or changed, leaves the count and the report unchanged. -/
theorem invariance (c : Contest) (bs : List Ballot)
    (h : (bs.map fun b : Ballot => b.positions).Perm (c.ballots.map fun b : Ballot => b.positions)) :
    countContest { c with ballots := bs } = countContest c ∧
      report { c with ballots := bs } = report c := by
  have hcount : countContest { c with ballots := bs } = countContest c := by
    simp only [countContest, count, kindsOf]
    exact run_perm h _ _
  have hlen : bs.length = c.ballots.length := by
    simpa using h.length_eq
  refine ⟨hcount, ?_⟩
  simp only [report, reportLines, hcount, headerLines, hlen]

theorem reportLines_order (c : Contest) :
    reportLines c =
      ([ascii "rcv-report 1", spaced [ascii "rule", ascii ruleIdentifier]] ++
          [spaced [ascii "contest", c.contest], spaced [ascii "positions", decimal c.positions],
            spaced [ascii "candidates", decimal c.candidates.length]] ++
          (c.candidates.zipIdx 1).map (fun p : Candidate × Nat =>
            spaced [ascii "candidate", decimal p.2, ascii (kindWord p.1.kind), p.1.name])) ++
        spaced (ascii "order" :: c.order.map decimal) ::
          ([spaced [ascii "ballots", decimal c.ballots.length]] ++
            (((countContest c).rounds.zipIdx 1).flatMap fun p : Round × Nat => roundLines p.2 p.1) ++
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
        reportLines { c with order := π' } = A ++ spaced (ascii "order" :: π'.map decimal) :: B := by
  have ht := count_trace (kindsOf c) c.order (c.ballots.map fun b : Ballot => b.positions)
  have hnd : π'.Nodup := hπ.nodup_iff.2 List.nodup_range'
  have hcount : countContest { c with order := π' } = countContest c := by
    simp only [countContest, count, kindsOf]
    apply run_order
    intro rd hrd Z i he
    obtain ⟨-, hsub, hrule⟩ := ht.mem rd hrd
    have hr := hrule _ he
    obtain ⟨hpos, -, hcases⟩ := rule_eq_eliminate hr
    have hZ : Z = ruleTied rd.tally.votes ∧ i = latest c.order (ruleTied rd.tally.votes) := by
      rcases hcases with ⟨s, -, hs⟩ | ⟨-, ⟨z, -, hz⟩ | ⟨-, hz⟩⟩
      · cases hs
      · cases hz
      · simp only [Elimination.order.injEq] at hz
        exact hz
    obtain ⟨rfl, rfl⟩ := hZ
    have hle := h rd hrd _ _ he
    rw [ruleTied_eq_fewest] at hle ⊢
    have hne := fewest_ne_nil (votes_ne_nil hpos)
    have hsubπ : ∀ j ∈ fewest rd.tally.votes, j ∈ π' := by
      intro j hj
      have hb := mem_countedSet (hsub.subset (fewest_sub hj))
      simp only [kindsOf, List.length_map] at hb
      exact hπ.mem_iff.2 (List.mem_range'_1.2 ⟨hb.1, by omega⟩)
    obtain ⟨hmem', hlast'⟩ := latest_spec hnd hsubπ hne
    have hmem : latest c.order (fewest rd.tally.votes) ∈ fewest rd.tally.votes := latest_mem hne
    have h1 := hle _ hmem'
    have h2 := (hlast' _ hmem).2
    exact idxOf_inj (hsubπ _ hmem') (hsubπ _ hmem) (by omega)
  refine ⟨hcount, _, _, reportLines_order c, ?_⟩
  rw [reportLines_order, hcount]

end Demos.Rcv.Rounds
