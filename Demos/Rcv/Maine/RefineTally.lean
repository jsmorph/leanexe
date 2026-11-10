import Demos.Rcv.Maine.Program
import Demos.Rcv.Maine.Spec
import Demos.Rcv.Refinement

/-!
The tally of a round of the Maine program: `Demos.Rcv.Maine.Program.examineAt` gives the slot of
`Demos.Rcv.Maine.interpret`, and `Demos.Rcv.Maine.Program.tallyRound` counts the ballots of each
slot.  The program counts the empty positions just passed, up to 2, where the specification looks
ahead from an empty position, so `examineAt_eq` states the program's examination from word `p`
after `g` empty positions as the specification's examination of `g` zero words followed by the words
from `p`: two zero words and a marked one end the examination with `exhausted`
(`examine_gap_two`), and a third zero word changes nothing (`examine_three_zeros`).  A ballot that
the Maine examination passes to its end passes the Oakland examination as well
(`examine_none_oakland`), so the Oakland refinement's `Demos.Rcv.Refine.passedSlot_eq` gives its
reason.
-/

namespace Demos.Rcv.Maine.Refine

open Demos.Rcv Demos.Rcv.Spec Demos.Rcv.Refine

/-! ## Runs of empty positions -/

theorem marked_zero : marked 0 = false := by
  simp [marked, position_zero]

theorem marked_of_ne {w : UInt64} (h : w ≠ 0) : marked w = true := by
  unfold marked
  cases hp : position w with
  | empty => exact absurd (position_empty hp) h
  | single i => rfl
  | multiple => rfl

theorem skipped_zero (ps : List UInt64) : skipped (0 :: ps) = ps.any marked := by
  simp [skipped, position_zero]

theorem skipped_ne {w : UInt64} (h : w ≠ 0) (ps : List UInt64) : skipped (w :: ps) = false := by
  show (position w == .empty && ps.any marked) = false
  cases hp : position w with
  | empty => exact absurd (position_empty hp) h
  | single i => rfl
  | multiple => rfl

theorem examine_zero (C : List Nat) (ps : List UInt64) :
    examine C (0 :: ps) = if skipped ps then some (.inactive .exhausted) else examine C ps := by
  simp only [examine, position_zero]

theorem any_marked_zeros : ∀ g : Nat, (List.replicate g (0 : UInt64)).any marked = false
  | 0 => rfl
  | g + 1 => by
    rw [List.replicate_succ, List.any_cons, marked_zero, any_marked_zeros g]
    rfl

theorem examine_zeros (C : List Nat) : ∀ g : Nat, examine C (List.replicate g (0 : UInt64)) = none
  | 0 => rfl
  | g + 1 => by
    have hs : skipped (List.replicate g (0 : UInt64)) = false := by
      cases g with
      | zero => rfl
      | succ g => rw [List.replicate_succ, skipped_zero, any_marked_zeros]
    rw [List.replicate_succ, examine_zero, hs, examine_zeros C g]
    rfl

/-- Two empty positions before a marked one end the examination with `exhausted`. -/
theorem examine_gap_two (C : List Nat) {w : UInt64} (hw : w ≠ 0) (ps : List UInt64) :
    examine C (0 :: 0 :: w :: ps) = some (.inactive .exhausted) := by
  rw [examine_zero, skipped_zero, List.any_cons, marked_of_ne hw]
  rfl

/-- At most one empty position before a marked one changes nothing. -/
theorem examine_gap_ne (C : List Nat) {w : UInt64} (hw : w ≠ 0) (ps : List UInt64) {g : Nat}
    (hg : g ≤ 1) : examine C (List.replicate g 0 ++ w :: ps) = examine C (w :: ps) := by
  rcases (show g = 0 ∨ g = 1 by omega) with rfl | rfl
  · rfl
  · rw [List.replicate_one, List.singleton_append, examine_zero, skipped_ne hw]
    rfl

/-- A third empty position changes nothing. -/
theorem examine_three_zeros (C : List Nat) (ps : List UInt64) :
    examine C (0 :: 0 :: 0 :: ps) = examine C (0 :: 0 :: ps) := by
  have e1 := examine_zero C (0 :: 0 :: ps)
  have e2 := examine_zero C (0 :: ps)
  rw [skipped_zero, List.any_cons, marked_zero, Bool.false_or] at e1
  rw [skipped_zero] at e2
  rw [e1, e2]
  by_cases h : ps.any marked = true
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

/-! ## One ballot -/

/-- `examineAt` from `p` to `e` after `g` empty positions, `g ≤ 2`, gives the slot of the
examination of `g` zero words and the words from `p`, or, when the examination passes them all,
the slot of the union of `seen` and the words. -/
theorem examineAt_eq (ws : Array UInt64) (cont counted : UInt64) (C : List Nat)
    (hC : ∀ i, 1 ≤ i → i ≤ 63 → (i ∈ C ↔ cont.toNat.testBit (i - 1) = true)) :
    ∀ (m : Nat) (p e seen g : UInt64), e.toNat = p.toNat + m → g.toNat ≤ 2 →
      Program.examineAt ws cont counted e p seen g =
        match examine C (List.replicate g.toNat 0 ++ wordsAt ws p.toNat m) with
        | some o => UInt64.ofNat (slot o)
        | none => passedSlot (seen ||| orAll (wordsAt ws p.toNat m)) counted := by
  intro m
  induction m with
  | zero =>
    intro p e seen g he _
    have hpe : e = p := UInt64.toNat_inj.mp (by omega)
    subst hpe
    rw [Program.examineAt, ite_eq_right (by simp)]
    simp only [wordsAt, List.range_zero, List.map_nil, List.append_nil, examine_zeros, orAll,
      List.foldr_nil, UInt64.or_zero, passedSlot]
  | succ m ih =>
    intro p e seen g he hg
    have hp : p < e := UInt64.lt_iff_toNat_lt.mpr (by omega)
    have hp1 : (p + 1).toNat = p.toNat + 1 := by
      have := UInt64.toNat_lt e
      simp only [UInt64.toNat_add, UInt64.toNat_one]
      omega
    have hrest := fun (s g' : UInt64) (hg' : g'.toNat ≤ 2) =>
      ih (p + 1) e s g' (by omega) hg'
    rw [hp1] at hrest
    rw [Program.examineAt, ite_eq_left hp]
    dsimp only
    rw [wordsAt_succ]
    generalize ws[p.toNat]! = w at hrest ⊢
    generalize wordsAt ws (p.toNat + 1) m = rest at hrest ⊢
    have hg3 : g = 0 ∨ g = 1 ∨ g = 2 := by
      have h0 : g.toNat = 0 ∨ g.toNat = 1 ∨ g.toNat = 2 := by omega
      rcases h0 with h0 | h0 | h0
      · exact Or.inl (UInt64.toNat_inj.mp h0)
      · exact Or.inr (Or.inl (UInt64.toNat_inj.mp h0))
      · exact Or.inr (Or.inr (UInt64.toNat_inj.mp h0))
    by_cases hw : w = 0
    · subst hw
      simp only [beq_self_eq_true, ↓reduceIte, orAll, List.foldr_cons, UInt64.zero_or]
      rcases hg3 with rfl | rfl | rfl
      · rw [show (if ((0 : UInt64) == 0) = true then (1 : UInt64) else 2) = 1 from rfl,
          hrest seen 1 (by decide)]
        rfl
      · rw [show (if ((1 : UInt64) == 0) = true then (1 : UInt64) else 2) = 2 from rfl,
          hrest seen 2 (by decide)]
        rfl
      · rw [show (if ((2 : UInt64) == 0) = true then (1 : UInt64) else 2) = 2 from rfl,
          hrest seen 2 (by decide)]
        show (match examine C (0 :: 0 :: rest) with
          | some o => UInt64.ofNat (slot o)
          | none => passedSlot (seen ||| orAll rest) counted) =
          match examine C (0 :: 0 :: 0 :: rest) with
          | some o => UInt64.ofNat (slot o)
          | none => passedSlot (seen ||| orAll rest) counted
        rw [examine_three_zeros]
    · have hw' : (w == 0) = false := by simpa using hw
      simp only [hw', Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : g = 2
      · subst h2
        simp only [beq_self_eq_true, ↓reduceIte]
        show (67 : UInt64) = match examine C (0 :: 0 :: w :: rest) with
          | some o => UInt64.ofNat (slot o)
          | none => passedSlot (seen ||| orAll (w :: rest)) counted
        rw [examine_gap_two C hw]
        rfl
      · have hg1 : g.toNat ≤ 1 := by
          rcases hg3 with rfl | rfl | rfl
          · decide
          · decide
          · exact absurd rfl h2
        have h2' : (g == 2) = false := by simpa using h2
        simp only [h2', Bool.false_eq_true, ↓reduceIte]
        rw [examine_gap_ne C hw rest hg1, classify_eq]
        have hr0 := hrest (seen ||| w) 0 (by decide)
        simp only [UInt64.toNat_zero, List.replicate_zero, List.nil_append] at hr0
        simp only [examine, orAll, List.foldr_cons]
        cases hpos : position w with
        | empty => exact absurd (position_empty hpos) hw
        | multiple => simp [slot]
        | single i =>
          obtain ⟨h1, h2, _⟩ := position_single hpos
          by_cases hb : cont.toNat.testBit (i - 1) = true
          · have hiC : i ∈ C := (hC i h1 h2).mpr hb
            have hne : (UInt64.ofNat i == 0) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]
              intro h
              have := congrArg UInt64.toNat h
              rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)] at this
              simp at this
              omega
            simp only [hb, ↓reduceIte, hne, Bool.false_eq_true, hiC, slot]
            apply UInt64.toNat_inj.mp
            rw [UInt64.toNat_sub_of_le _ _ (by
                rw [UInt64.le_iff_toNat_le,
                  UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
                simp
                omega)]
            rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega),
              UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
            simp
          · have hiC : i ∉ C := fun h => hb ((hC i h1 h2).mp h)
            simp only [hb, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, hiC]
            rw [hr0]
            split <;> simp [UInt64.or_assoc, orAll]

/-- A ballot that the Maine examination passes to its end passes the Oakland examination. -/
theorem examine_none_oakland {C : List Nat} :
    ∀ {ps : List UInt64}, examine C ps = none → Spec.examine C ps = none
  | [], _ => rfl
  | w :: ps, h => by
    cases hp : position w with
    | empty =>
      simp only [examine, hp] at h
      by_cases hs : skipped ps = true
      · rw [ite_eq_left hs] at h
        cases h
      · rw [ite_eq_right hs] at h
        simp only [Spec.examine, hp]
        exact examine_none_oakland h
    | multiple => simp [examine, hp] at h
    | single i =>
      simp only [examine, hp] at h
      by_cases hi : i ∈ C
      · rw [ite_eq_left hi] at h
        cases h
      · rw [ite_eq_right hi] at h
        simp only [Spec.examine, hp, ite_eq_right hi]
        exact examine_none_oakland h

theorem examine_valid {C : List Nat} :
    ∀ {ps : List UInt64} {o : Outcome}, examine C ps = some o → validOutcome o
  | [], _, h => by simp [examine] at h
  | w :: ps, o, h => by
    cases hp : position w with
    | empty =>
      simp only [examine, hp] at h
      split at h
      · cases h
        trivial
      · exact examine_valid h
    | multiple =>
      simp only [examine, hp, Option.some.injEq] at h
      subst h
      trivial
    | single i =>
      simp only [examine, hp] at h
      split at h
      · cases h
        obtain ⟨h1, h2, _⟩ := position_single hp
        exact ⟨h1, h2⟩
      · exact examine_valid h

theorem interpret_valid (kinds : List Kind) (C : List Nat) (ps : List UInt64) :
    validOutcome (interpret kinds C ps) := by
  unfold interpret
  cases h : examine C ps with
  | none => trivial
  | some o => exact examine_valid h

/-- `examineAt` over `m` words from `p`, from an empty union and no empty position before them,
gives the slot of the interpretation of the words. -/
theorem examineAt_interpret (ws : Array UInt64) (cont counted : UInt64) (kinds : List Kind)
    (C : List Nat)
    (hC : ∀ i, 1 ≤ i → i ≤ 63 → (i ∈ C ↔ cont.toNat.testBit (i - 1) = true))
    (hK : ∀ i, 1 ≤ i → i ≤ 63 →
      (i ∈ countedSet kinds ↔ counted.toNat.testBit (i - 1) = true))
    (m : Nat) (p e : UInt64) (he : e.toNat = p.toNat + m) :
    Program.examineAt ws cont counted e p 0 0 =
      UInt64.ofNat (slot (interpret kinds C (wordsAt ws p.toNat m))) := by
  rw [examineAt_eq ws cont counted C hC m p e 0 0 he (by decide)]
  simp only [UInt64.toNat_zero, List.replicate_zero, List.nil_append]
  unfold interpret
  cases h : examine C (wordsAt ws p.toNat m) with
  | some o => rfl
  | none =>
    simp only [Option.getD_none]
    rw [UInt64.zero_or]
    exact passedSlot_eq hK (examine_none_oakland h)

/-! ## The counters of a round -/

/-- The first `m` words of ballot `b`, whose words start at word `q + b k`. -/
def ballotPart (ws : Array UInt64) (q k m b : Nat) : List UInt64 := wordsAt ws (q + b * k) m

theorem tallyRound_eq (ws : Array UInt64) (cont counted k m N base : UInt64) (kinds : List Kind)
    (C : List Nat)
    (hC : ∀ i, 1 ≤ i → i ≤ 63 → (i ∈ C ↔ cont.toNat.testBit (i - 1) = true))
    (hK : ∀ i, 1 ≤ i → i ≤ 63 →
      (i ∈ countedSet kinds ↔ counted.toNat.testBit (i - 1) = true))
    (hm : m.toNat ≤ k.toNat) (hfit : base.toNat + N.toNat * k.toNat < 2 ^ 64) :
    (Program.tallyRound ws cont counted k m N base).size = 68 ∧
      ∀ s, s < 68 → (Program.tallyRound ws cont counted k m N base)[s]!.toNat =
        (((List.range N.toNat).map fun b => ballotPart ws base.toNat k.toNat m.toNat b).map
          (interpret kinds C)).countP fun o => slot o = s := by
  unfold Program.tallyRound
  have hinv := LeanExe.Dialect.loop_induction (n := N)
    (init := LeanExe.build 68 fun _ => (0 : UInt64))
    (f := fun b t =>
      let p := base + b * k
      let s := Program.examineAt ws cont counted (p + m) p 0 0
      t.set! s.toNat (t[s.toNat]! + 1))
    (fun j t => t.size = 68 ∧ ∀ s, s < 68 → t[s]!.toNat =
      (((List.range j).map fun b => ballotPart ws base.toNat k.toNat m.toNat b).map
        (interpret kinds C)).countP fun o => slot o = s)
    ⟨by simp [LeanExe.Dialect.build_size], fun s hs => by
      rw [LeanExe.Dialect.build_get (by simpa using hs)]
      simp⟩
    (fun j t hj ⟨hsize, hcnt⟩ => by
      have hjk : j * k.toNat ≤ N.toNat * k.toNat := Nat.mul_le_mul_right _ (by omega)
      have hk1 : (j + 1) * k.toNat ≤ N.toNat * k.toNat := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at hk1
      have hp : (base + UInt64.ofNat j * k).toNat = base.toNat + j * k.toNat := by
        simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (show j < 2 ^ 64 by have := UInt64.toNat_lt N; omega)]
        rw [Nat.mod_eq_of_lt (show j * k.toNat < 2 ^ 64 by omega)]
        omega
      have he : (base + UInt64.ofNat j * k + m).toNat =
          (base + UInt64.ofNat j * k).toNat + m.toNat := by
        rw [UInt64.toNat_add, hp]
        omega
      have hs := examineAt_interpret ws cont counted kinds C hC hK m.toNat _ _ he
      dsimp only
      rw [hs, hp]
      set o := interpret kinds C (wordsAt ws (base.toNat + j * k.toNat) m.toNat) with ho
      have hvalid : validOutcome o := interpret_valid _ _ _
      have hslot := slot_lt hvalid
      have hsl : (UInt64.ofNat (slot o)).toNat = slot o :=
        UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
      rw [hsl]
      refine ⟨by simp [hsize], fun s hs' => ?_⟩
      rw [LeanExe.Dialect.get_set _ _ _ _ (by omega), List.range_succ, List.map_append,
        List.map_append, List.countP_append]
      simp only [List.map_cons, List.map_nil, List.countP_cons, List.countP_nil, Nat.zero_add]
      have hle : (((List.range j).map fun b => ballotPart ws base.toNat k.toNat m.toNat b).map
          (interpret kinds C)).countP (fun o => slot o = s) ≤ j := by
        refine (List.countP_le_length).trans ?_
        simp
      have hlt : j < 2 ^ 64 - 1 := by have := UInt64.toNat_lt N; omega
      by_cases hss : s = slot o
      · subst hss
        simp only [↓reduceIte]
        rw [UInt64.toNat_add, hcnt _ hs', UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
        simp [ballotPart, ← ho]
      · rw [ite_eq_right hss, hcnt s hs']
        simp only [ballotPart]
        have : ¬ (slot o = s) := fun h => hss h.symm
        simp [← ho, this])
  exact hinv

end Demos.Rcv.Maine.Refine
