import Demos.Rcv.Maine.RefineRule

/-!
The refinement of the Maine count over words: `count_eq` states that
`Demos.Rcv.Maine.Program.count`, the program that the module compiles, equals
`Demos.Rcv.Maine.countArray` on every array of fewer than `2 ^ 64` words.  The program tests the
array with the Oakland program's `validArray`, which `Demos.Rcv.Refine.validArray_iff` equates with
`Demos.Rcv.Spec.Words.Valid`.  `first_eq` shows that the counters of the round of the first
positions against `K` hold the first counts `f(i)`, `majorityOf` then gives the initial test's
winner, and `go_eq` follows the `repeatWhile` of the rounds against `Demos.Rcv.Spec.run` with
`Demos.Rcv.Maine.decision`, a round at a time, as the Oakland refinement's `go_eq` does with
`Demos.Rcv.Spec.rule`.
-/

namespace Demos.Rcv.Maine.Refine

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Refine Demos.Rcv.Rounds

/-! ## The rounds -/

/-- The candidate that a round eliminates is a member of its continuing set. -/
theorem eliminated_sublist {order C : List Nat} {v : Nat → Nat} {tl : Tally}
    (hvotes : tl.votes = C.map fun i => (i, v i)) {el : Elimination}
    (h : decision order tl = .eliminate el) : el.eliminated.Sublist C := by
  obtain ⟨-, hmem⟩ := (decision_ends order).1 tl el h
  have hfst : tl.votes.map (fun x : Nat × Nat => x.1) = C := by
    rw [hvotes, List.map_map]
    exact List.map_id C
  rw [hfst] at hmem
  have hone : ∃ i, el.eliminated = [i] := by
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
  obtain ⟨i, hi⟩ := hone
  rw [hi] at hmem ⊢
  exact List.singleton_sublist.mpr (hmem i (List.mem_singleton_self i))

/-- The loop of the rounds in `countValid`. -/
def roundsGo (ws : Array UInt64) (n k N counted : UInt64) (f : Nat)
    (s : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 :=
  LeanExe.repeatWhile.go
    (fun s : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64 => s.2.1 == 0)
    (fun s => Program.roundStep ws n k N counted s) f s

theorem roundsGo_stop (ws : Array UInt64) (n k N counted : UInt64)
    (s : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64) (h : (s.2.1 == 0) = false) :
    ∀ f, roundsGo ws n k N counted f s = s
  | 0 => rfl
  | f + 1 => by
    unfold roundsGo
    rw [LeanExe.repeatWhile.go, ite_eq_right (by simp [h])]

theorem go_eq (ws : Array UInt64) (n k N counted : UInt64) (kinds : List Kind) (order : List Nat)
    (hn : n.toNat ≤ 63) (hk : k.toNat ≤ 63) (hN : N.toNat < 2 ^ 32)
    (hK : ∀ i, 1 ≤ i → i ≤ 63 →
      (i ∈ countedSet kinds ↔ counted.toNat.testBit (i - 1) = true))
    (horder : order = (List.range n.toNat).map fun j => (ws[3 + n.toNat + j]!).toNat)
    (hperm : order.Perm (List.range' 1 n.toNat)) :
    ∀ (f : Nat) (cont r : UInt64) (out : Array UInt64), cont.toNat < 2 ^ n.toNat →
      r.toNat + f < 2 ^ 64 →
      (roundsGo ws n k N counted f (cont, 0, 0, r, out)).2.2.1 =
          UInt64.ofNat ((run (interpret kinds) (decision order)
            (ballotsOf ws n.toNat k.toNat N.toNat) f (members cont n.toNat)).winner.getD 0) ∧
        (roundsGo ws n k N counted f (cont, 0, 0, r, out)).2.2.2.1.toNat =
          r.toNat + (run (interpret kinds) (decision order) (ballotsOf ws n.toNat k.toNat N.toNat)
            f (members cont n.toNat)).rounds.length ∧
        (roundsGo ws n k N counted f (cont, 0, 0, r, out)).2.2.2.2.toList =
          out.toList ++
            ((run (interpret kinds) (decision order) (ballotsOf ws n.toNat k.toNat N.toNat) f
            (members cont n.toNat)).rounds.flatMap (roundWords n.toNat)).map Nat.toUInt64 := by
  intro f
  induction f with
  | zero =>
    intro cont r out _ _
    simp [roundsGo, LeanExe.repeatWhile.go, run]
  | succ f ih =>
    intro cont r out hc hr
    have hgo : roundsGo ws n k N counted (f + 1) (cont, 0, 0, r, out) =
        roundsGo ws n k N counted f (Program.roundStep ws n k N counted (cont, 0, 0, r, out)) := by
      unfold roundsGo
      rw [LeanExe.repeatWhile.go, ite_eq_left (by simp)]
    rw [hgo]
    simp only [Program.roundStep]
    have hCbit : ∀ i, 1 ≤ i → i ≤ 63 →
        (i ∈ members cont n.toNat ↔ cont.toNat.testBit (i - 1) = true) := by
      intro i h1 h2
      rw [mem_members]
      constructor
      · rintro ⟨_, _, h⟩
        exact h
      · intro h
        refine ⟨h1, ?_, h⟩
        by_contra hgt
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num)
          (by omega)))] at h
        cases h
    have h3 : (3 + 2 * n).toNat = 3 + 2 * n.toNat := by
      simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, Nat.reducePow]
      omega
    have hfit : (3 + 2 * n).toNat + N.toNat * k.toNat < 2 ^ 64 := by
      have : N.toNat * k.toNat ≤ 4294967295 * 63 := Nat.mul_le_mul (by omega) hk
      rw [h3]
      norm_num
      omega
    obtain ⟨hsize, hcnt⟩ := tallyRound_eq ws cont counted k k N (3 + 2 * n) kinds
      (members cont n.toNat) hCbit hK (le_refl _) hfit
    rw [h3] at hcnt
    generalize htl : Program.tallyRound ws cont counted k k N (3 + 2 * n) = t at hsize hcnt ⊢
    have hb : ((List.range N.toNat).map fun b =>
        ballotPart ws (3 + 2 * n.toNat) k.toNat k.toNat b) = ballotsOf ws n.toNat k.toNat N.toNat :=
      rfl
    rw [hb] at hcnt
    have hvalid : ∀ o ∈ (ballotsOf ws n.toNat k.toNat N.toNat).map
        (interpret kinds (members cont n.toNat)), validOutcome o := by
      intro o ho
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ho
      exact interpret_valid _ _ _
    have ht : Votes t fun i => ((ballotsOf ws n.toNat k.toNat N.toNat).map
        (interpret kinds (members cont n.toNat))).count (.counts i) := by
      constructor
      · intro i h1 h2
        rw [hcnt (i - 1) (by omega)]
        exact count_slot hvalid (o := .counts i) ⟨h1, h2⟩
      · intro i
        have := List.count_le_length (a := Outcome.counts i)
          (l := (ballotsOf ws n.toNat k.toNat N.toNat).map
            (interpret kinds (members cont n.toNat)))
        simp only [ballotsOf, List.length_map, List.length_range] at this ⊢
        omega
    set tl := tally (interpret kinds) (members cont n.toNat)
      (ballotsOf ws n.toNat k.toNat N.toNat) with htldef
    have hvotes : tl.votes = (members cont n.toNat).map fun i => (i,
        ((ballotsOf ws n.toNat k.toNat N.toNat).map
          (interpret kinds (members cont n.toNat))).count (.counts i)) := rfl
    have hT := continuingOf_eq ht cont n hn
    have hT' : (Demos.Rcv.Program.continuingOf t cont n).toNat = tl.continuing := by
      rw [hT]
      simp only [Tally.continuing, hvotes, List.map_map]
      rfl
    rw [decideRound_eq ws t ht cont n hn hc tl hvotes order horder hperm]
    have hslot : ∀ (o : Outcome), validOutcome o → t[slot o]!.toNat =
        ((ballotsOf ws n.toNat k.toNat N.toNat).map
          (interpret kinds (members cont n.toNat))).count o := fun o ho => by
      rw [hcnt (slot o) (slot_lt ho)]
      exact count_slot hvalid ho
    have hpush := fun (el : Option Elimination) (code elim tie : UInt64)
        (hel : [code, elim, tie] = (elimTail el).map Nat.toUInt64) =>
      pushRound_eq out t cont (Demos.Rcv.Program.continuingOf t cont n) n hn hc tl ht hvotes hT'
        (hslot (.inactive .blank) trivial) (hslot (.inactive .uncounted) trivial)
        (hslot (.inactive .overvote) trivial) (hslot (.inactive .exhausted) trivial) el code elim
        tie hel
    have hrun : run (interpret kinds) (decision order) (ballotsOf ws n.toNat k.toNat N.toNat)
        (f + 1) (members cont n.toNat) =
        match decision order tl with
        | .winner w => ⟨[⟨tl, none⟩], w⟩
        | .eliminate e =>
          let rest : Count := run (interpret kinds) (decision order)
            (ballotsOf ws n.toNat k.toNat N.toNat) f
            ((members cont n.toNat).filter fun i : Nat => decide (i ∉ e.eliminated))
          ⟨⟨tl, some e⟩ :: rest.rounds, rest.winner⟩ := rfl
    rw [hrun]
    cases hdec : decision order tl with
    | winner w =>
      rw [show endWords (.winner w) = (0, 0, 0, UInt64.ofNat (w.getD 0)) from rfl]
      simp only [beq_self_eq_true, ↓reduceIte]
      have hstop := roundsGo_stop ws n k N counted
        (cont, 1, UInt64.ofNat (w.getD 0), r + 1,
          Demos.Rcv.Program.pushRound out t cont (Demos.Rcv.Program.continuingOf t cont n) n 0 0 0)
        (by simp) f
      rw [hstop]
      refine ⟨rfl, ?_, ?_⟩
      · simp only [List.length_singleton]
        rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
      · show (Demos.Rcv.Program.pushRound out t cont (Demos.Rcv.Program.continuingOf t cont n) n 0
          0 0).toList = _
        rw [hpush none 0 0 0 rfl]
        simp
    | eliminate el =>
      obtain ⟨hel, hcode⟩ := endWords_eliminate el
      have hcode' : ((endWords (.eliminate el)).1 == 0) = false := by simpa using hcode
      simp only [hcode', Bool.false_eq_true, ↓reduceIte]
      have hsub := eliminated_sublist hvotes hdec
      have hsubr : el.eliminated.Sublist (List.range' 1 n.toNat) :=
        hsub.trans (members_sublist cont n.toNat)
      have hmr := members_remove cont (endWords (.eliminate el)).2.1 n.toNat el.eliminated hsubr hn
        (by rw [hel, ofNat_toNat_lt (lt_of_lt_of_le (mask_lt hsubr)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))])
      have hc' : (cont &&& ((endWords (.eliminate el)).2.1 ^^^ 0xFFFFFFFFFFFFFFFF)).toNat <
          2 ^ n.toNat := by
        rw [UInt64.toNat_and]
        exact lt_of_le_of_lt Nat.and_le_left hc
      have hr1 : (r + 1).toNat = r.toNat + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
      obtain ⟨i1, i2, i3⟩ := ih _ (r + 1)
        (Demos.Rcv.Program.pushRound out t cont (Demos.Rcv.Program.continuingOf t cont n) n
          (endWords (.eliminate el)).1 (endWords (.eliminate el)).2.1
          (endWords (.eliminate el)).2.2.1) hc' (by omega)
      rw [hmr] at i1 i2 i3
      refine ⟨i1, ?_, ?_⟩
      · rw [i2, hr1]
        simp only [List.length_cons]
        omega
      · rw [i3, hpush (some el) _ _ _ (endWords_tail_eliminate el)]
        simp

/-! ## The first counts -/

/-- Against a continuing set that holds `i`, a ballot of one position counts for `i` exactly when
the position is single and marks `i`. -/
theorem interpret_single {kinds : List Kind} {K : List Nat} {w : UInt64} {i : Nat} (hi : i ∈ K) :
    (interpret kinds K [w] == .counts i) = (position w == .single i) := by
  unfold interpret
  cases hp : position w with
  | empty =>
    simp only [examine, hp, skipped, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
    rfl
  | multiple =>
    simp only [examine, hp, Option.getD_some]
    rfl
  | single j =>
    simp only [examine, hp]
    by_cases hj : j ∈ K
    · rw [ite_eq_left hj, Option.getD_some]
      by_cases hji : j = i
      · subst hji
        simp
      · simp [hji]
    · rw [ite_eq_right hj]
      have hji : j ≠ i := fun h => hj (h ▸ hi)
      simp [hji]

/-- The votes of the round of the first positions against `K` are the first counts. -/
theorem first_count (ws : Array UInt64) (kinds : List Kind) (q k N : Nat) (hk : 1 ≤ k) (i : Nat) :
    (((List.range N).map fun b => ballotPart ws q k 1 b).map
        (interpret kinds (countedSet kinds))).count (.counts i) =
      if i ∈ countedSet kinds then
        (((List.range N).map fun b => ballotAt ws q k b).map firstPosition).count (.single i)
      else 0 := by
  by_cases hi : i ∈ countedSet kinds
  · rw [ite_eq_left hi, List.count_eq_countP, List.count_eq_countP, List.countP_map,
      List.countP_map, List.countP_map, List.countP_map]
    apply List.countP_congr
    intro b _
    have h1 : ballotPart ws q k 1 b = [ws[q + b * k]!] := by
      simp [ballotPart, wordsAt]
    have h2 : firstPosition (ballotAt ws q k b) = position ws[q + b * k]! := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [ballotAt, wordsAt_succ, firstPosition]
    simp only [Function.comp_apply, h1, h2]
    rw [interpret_single (kinds := kinds) hi]
  · rw [ite_eq_right hi, List.count_eq_zero]
    intro hm
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hm
    exact hi (Demos.Rcv.Maine.interpret_counts hb)

theorem find?_congr {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      find?_congr (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-! ## The count -/

/-- The result words of `countValid` on a valid contest array are those of the specification's
count. -/
theorem countValid_eq (ws : Array UInt64) (hs : ws.size < 2 ^ 64)
    (hv : (readWords ws.toList).Valid ws.toList.length) :
    Program.countValid ws =
      (resultWords (readWords ws.toList).n
        (firstCounts ((readWords ws.toList).kinds.map kindOfCode) (readWords ws.toList).ballots)
        (count ((readWords ws.toList).kinds.map kindOfCode) (readWords ws.toList).order
          (readWords ws.toList).ballots)).toArray := by
  have hcv : Program.countValid ws =
      let first := Program.tallyRound ws (Demos.Rcv.Program.countedOf ws ws[0]!)
        (Demos.Rcv.Program.countedOf ws ws[0]!) ws[1]! (1 : UInt64) ws[2]!
        ((3 : UInt64) + (2 : UInt64) * ws[0]!)
      let out := LeanExe.loop ws[0]! #[(1 : UInt64), 0] fun c o => o.push first[c.toNat]!
      let w := Demos.Rcv.Program.majorityOf first (Demos.Rcv.Program.countedOf ws ws[0]!) ws[2]!
        ws[0]!
      if w != 0 then out.push w
      else
        let s := roundsGo ws ws[0]! ws[1]! ws[2]! (Demos.Rcv.Program.countedOf ws ws[0]!)
          (Demos.Rcv.Program.countedSize ws ws[0]! + 1).toNat
          (Demos.Rcv.Program.countedOf ws ws[0]!, (0 : UInt64), (0 : UInt64), (0 : UInt64), out)
        (s.2.2.2.2.set! 1 s.2.2.2.1).push s.2.2.1 := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, -, hperm, -⟩ := hv
  rw [readWords_n, readWords_k, readWords_N] at *
  simp only [maxIndex, maxBallots, Array.length_toList] at h2 h4 h5 h6
  have hkinds : (readWords ws.toList).kinds = (wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat := by
    simp only [readWords, getD_toList]
    rw [take_drop_eq_wordsAt ws 3 _ (by omega)]
  have horder : (readWords ws.toList).order =
      (List.range ws[0]!.toNat).map fun j => (ws[3 + ws[0]!.toNat + j]!).toNat := by
    simp only [readWords, getD_toList]
    rw [take_drop_eq_wordsAt ws _ _ (by omega), wordsAt_map_toNat]
  have hballots : (readWords ws.toList).ballots =
      ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat := by
    simp only [Words.ballots, readWords, getD_toList]
    exact chunks_eq ws _ _ _ (by omega)
  have hn : ws[0]!.toNat ≤ 63 := h2
  have hK := countedSet_eq ws ws[0]!.toNat
  have hcount := countedOf_eq ws ws[0]! hn
  have hsize := countedSize_eq ws ws[0]! hn
  have hmem := members_counted ws ws[0]! hn
  have hsub : (countedOfWords ws ws[0]!.toNat).Sublist (List.range' 1 ws[0]!.toNat) :=
    List.filter_sublist
  have hKlen : (countedOfWords ws ws[0]!.toNat).length ≤ 63 :=
    (hsub.length_le.trans (by simp)).trans hn
  have hfuel : (Demos.Rcv.Program.countedSize ws ws[0]! + 1).toNat =
      (countedOfWords ws ws[0]!.toNat).length + 1 := by
    rw [UInt64.toNat_add, hsize, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
  have hcK : (Demos.Rcv.Program.countedOf ws ws[0]!).toNat < 2 ^ ws[0]!.toNat := by
    rw [hcount]
    exact mask_lt hsub
  have hKbit : ∀ i, 1 ≤ i → i ≤ 63 →
      (i ∈ countedSet (((wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat).map kindOfCode) ↔
        (Demos.Rcv.Program.countedOf ws ws[0]!).toNat.testBit (i - 1) = true) := by
    intro i hi1 _
    rw [hK, hcount, testBit_mask_sublist hsub, Nat.sub_add_cancel hi1]
    simp
  have hperm' : ((List.range ws[0]!.toNat).map fun j => (ws[3 + ws[0]!.toNat + j]!).toNat).Perm
      (List.range' 1 ws[0]!.toNat) := by
    rw [← horder]
    exact hperm
  have h3 : ((3 : UInt64) + (2 : UInt64) * ws[0]!).toNat = 3 + 2 * ws[0]!.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat, Nat.reducePow]
    omega
  have hfit :
      ((3 : UInt64) + (2 : UInt64) * ws[0]!).toNat + ws[2]!.toNat * ws[1]!.toNat < 2 ^ 64 := by
    have : ws[2]!.toNat * ws[1]!.toNat ≤ 4294967295 * 63 :=
      Nat.mul_le_mul (by norm_num at h5; omega) h4
    rw [h3]
    norm_num
    omega
  rw [hcv, hkinds, horder, hballots]
  dsimp only
  rw [← hK] at hmem hfuel
  generalize ((wordsAt ws 3 ws[0]!.toNat).map UInt64.toNat).map kindOfCode = kinds
    at hKbit hmem hfuel ⊢
  generalize hord : ((List.range ws[0]!.toNat).map fun j => (ws[3 + ws[0]!.toNat + j]!).toNat) =
    order at hperm' ⊢
  have hKl : (countedSet kinds).length ≤ 63 := by
    rw [← hmem]
    exact (length_members _ _).trans hn
  -- The first counts
  obtain ⟨-, fcnt⟩ := tallyRound_eq ws (Demos.Rcv.Program.countedOf ws ws[0]!)
    (Demos.Rcv.Program.countedOf ws ws[0]!) ws[1]! 1 ws[2]!
    ((3 : UInt64) + (2 : UInt64) * ws[0]!) kinds
    (countedSet kinds) hKbit hKbit (by simp; omega) hfit
  rw [h3] at fcnt
  generalize Program.tallyRound ws (Demos.Rcv.Program.countedOf ws ws[0]!)
    (Demos.Rcv.Program.countedOf ws ws[0]!) ws[1]! 1 ws[2]!
    ((3 : UInt64) + (2 : UInt64) * ws[0]!) = first at fcnt ⊢
  set vf : Nat → Nat := fun i => (((List.range ws[2]!.toNat).map fun b =>
    ballotPart ws (3 + 2 * ws[0]!.toNat) ws[1]!.toNat (UInt64.toNat 1) b).map
      (interpret kinds (countedSet kinds))).count (.counts i) with hvf
  have hvalid : ∀ o ∈ ((List.range ws[2]!.toNat).map fun b =>
      ballotPart ws (3 + 2 * ws[0]!.toNat) ws[1]!.toNat (UInt64.toNat 1) b).map
        (interpret kinds (countedSet kinds)), validOutcome o := by
    intro o ho
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ho
    exact interpret_valid _ _ _
  have ht : Votes first vf := by
    constructor
    · intro i hi1 hi2
      rw [fcnt (i - 1) (by omega)]
      exact count_slot hvalid (o := .counts i) ⟨hi1, hi2⟩
    · intro i
      have := List.count_le_length (a := Outcome.counts i)
        (l := ((List.range ws[2]!.toNat).map fun b =>
          ballotPart ws (3 + 2 * ws[0]!.toNat) ws[1]!.toNat (UInt64.toNat 1) b).map
            (interpret kinds (countedSet kinds)))
      simp only [List.length_map, List.length_range] at this
      rw [hvf]
      beta_reduce
      norm_num at h5
      omega
  have hvfc : ∀ i, vf i = if i ∈ countedSet kinds then
      ((ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat).map firstPosition).count (.single i)
      else 0 := fun i => first_count ws kinds _ _ _ (by omega) i
  have hlook : ∀ i, ((firstCounts kinds (ballotsOf ws ws[0]!.toNat ws[1]!.toNat
      ws[2]!.toNat)).lookup i).getD 0 = vf i := by
    intro i
    rw [hvfc i]
    unfold firstCounts
    rw [lookup_map]
    split <;> rfl
  have hout : (LeanExe.loop ws[0]! #[(1 : UInt64), 0] fun c o => o.push first[c.toNat]!).toList =
      [(1 : UInt64), 0] ++ ((List.range' 1 ws[0]!.toNat).map fun i =>
        ((firstCounts kinds (ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat)).lookup
          i).getD 0).map Nat.toUInt64 := by
    rw [loop_eq_foldl, foldl_range_congr (g := fun o i => o.push first[i]!) (fun i hi s => by
      simp only [ofNat_toNat_lt (show i < 2 ^ 64 by omega)]), foldl_push]
    simp only [List.range'_eq_map_range, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    simp only [Function.comp_apply, hlook]
    have hg := ht.get (i + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at hg
    rw [Nat.add_comm 1 i]
    exact (toUInt64_eq hg).symm
  generalize LeanExe.loop ws[0]! #[(1 : UInt64), 0] (fun c o => o.push first[c.toNat]!) = out
    at hout ⊢
  -- The initial test
  have hlen : (ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat).length = ws[2]!.toNat := by
    simp [ballotsOf]
  have hinit : initialWinner kinds (ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat) =
      (countedSet kinds).find? (fun i => decide (ws[2]!.toNat < 2 * vf i)) := by
    unfold initialWinner firstCounts
    rw [List.find?_map, Option.map_map, hlen]
    have hfc : (countedSet kinds).find? ((fun x : Nat × Nat => decide (ws[2]!.toNat < 2 * x.2)) ∘
        fun i => (i, ((ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat).map
          firstPosition).count (.single i))) =
        (countedSet kinds).find? (fun i => decide (ws[2]!.toNat < 2 * vf i)) := by
      apply find?_congr
      intro i hi
      simp only [Function.comp_apply, hvfc i, ite_eq_left hi]
    rw [hfc]
    cases (countedSet kinds).find? (fun i => decide (ws[2]!.toNat < 2 * vf i)) <;> rfl
  have hmaj := majorityOf_eq ht (Demos.Rcv.Program.countedOf ws ws[0]!) ws[2]! ws[0]! hn
  rw [hmem] at hmaj
  cases hfind : (countedSet kinds).find? (fun i => decide (ws[2]!.toNat < 2 * vf i)) with
  | some w0 =>
    rw [hfind] at hmaj hinit
    have hw0 : w0 ∈ members (Demos.Rcv.Program.countedOf ws ws[0]!) ws[0]!.toNat := by
      rw [hmem]
      exact List.mem_of_find?_eq_some hfind
    have hwr := members_range hn hw0
    have hne : (UInt64.ofNat w0 != 0) = true := by
      rw [bne_iff_ne, ne_eq, ← UInt64.toNat_inj, ofNat_toNat_lt (by omega)]
      simp
      omega
    simp only [hmaj, hne, ↓reduceIte]
    rw [count_initial hinit]
    apply Array.toList_inj.mp
    rw [Array.toList_push, hout]
    simp [resultWords]
  | none =>
    rw [hfind] at hmaj hinit
    simp only [hmaj, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨g1, g2, g3⟩ := go_eq ws ws[0]! ws[1]! ws[2]! (Demos.Rcv.Program.countedOf ws ws[0]!)
      kinds order hn h4 (by norm_num at h5; omega) hKbit hord.symm hperm'
      ((countedSet kinds).length + 1) (Demos.Rcv.Program.countedOf ws ws[0]!) 0 out hcK
      (by simp; omega)
    rw [hmem] at g1 g2 g3
    rw [hfuel, count_run hinit]
    apply Array.toList_inj.mp
    simp only [Array.toList_push, Array.toList_set!]
    rw [g3, hout]
    generalize run (interpret kinds) (decision order)
      (ballotsOf ws ws[0]!.toNat ws[1]!.toNat ws[2]!.toNat) ((countedSet kinds).length + 1)
      (countedSet kinds) = c at g1 g2 ⊢
    rw [UInt64.toNat_zero, Nat.zero_add] at g2
    rw [g1, ← toUInt64_eq g2]
    simp [resultWords]

/-- The program equals the specification's export over words on every array of fewer than
`2 ^ 64` words, which every array in memory is. -/
theorem count_eq (ws : Array UInt64) (hs : ws.size < 2 ^ 64) :
    Program.count ws = countArray ws := by
  unfold Program.count countArray countWords
  by_cases hv : Demos.Rcv.Program.validArray ws = true
  · rw [ite_eq_left hv, ite_eq_left ((validArray_iff ws hs).mp hv)]
    exact countValid_eq ws hs ((validArray_iff ws hs).mp hv)
  · have hnv : ¬ (readWords ws.toList).Valid ws.toList.length := fun h =>
      hv ((validArray_iff ws hs).mpr h)
    rw [ite_eq_right hv, ite_eq_right hnv]

end Demos.Rcv.Maine.Refine
