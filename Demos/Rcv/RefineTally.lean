import Demos.Rcv.RefineBits
import LeanExe.Dialect.ArrayLemmas

/-!
The tally of a round: `Demos.Rcv.Program.examineAt` gives the slot of `Demos.Rcv.Spec.interpret`,
and `Demos.Rcv.Program.tallyRound` counts the ballots of each slot.
-/

namespace Demos.Rcv.Refine

open Demos.Rcv Demos.Rcv.Spec

/-- The tally slot of an outcome: `i - 1` for a vote for candidate `i`, and 64 to 67 for the
reasons `blank`, `uncounted`, `overvote`, and `exhausted`. -/
def slot : Outcome → Nat
  | .counts i => i - 1
  | .inactive .blank => 64
  | .inactive .uncounted => 65
  | .inactive .overvote => 66
  | .inactive .exhausted => 67

/-- An outcome that the interpretation can give: a vote for a candidate from 1 to 63, or a
reason. -/
def validOutcome : Outcome → Prop
  | .counts i => 1 ≤ i ∧ i ≤ 63
  | .inactive _ => True

theorem slot_lt {o : Outcome} (h : validOutcome o) : slot o < 68 := by
  rcases o with i | r
  · simp only [validOutcome] at h
    simp only [slot]
    omega
  · cases r <;> simp [slot]

theorem slot_inj {o o' : Outcome} (h : validOutcome o) (h' : validOutcome o')
    (hs : slot o = slot o') : o = o' := by
  rcases o with i | r <;> rcases o' with i' | r'
  · simp only [validOutcome, slot] at h h' hs
    congr 1
    omega
  · cases r' <;> simp only [validOutcome, slot] at h hs <;> omega
  · cases r <;> simp only [validOutcome, slot] at h' hs <;> omega
  · cases r <;> cases r' <;> simp_all [slot]

/-- The union of a list of words. -/
def orAll (l : List UInt64) : UInt64 := l.foldr (· ||| ·) 0

theorem orAll_eq_zero {l : List UInt64} : orAll l = 0 ↔ ∀ w ∈ l, w = 0 := by
  induction l with
  | nil => simp [orAll]
  | cons w l ih =>
    simp only [orAll, List.foldr_cons] at ih ⊢
    rw [List.forall_mem_cons, ← ih, ← UInt64.toNat_inj, ← UInt64.toNat_inj,
      ← UInt64.toNat_inj,
      UInt64.toNat_or, UInt64.toNat_zero, Nat.or_eq_zero_iff]

theorem orAll_and_ne_zero {l : List UInt64} (c : UInt64) :
    (orAll l &&& c).toNat ≠ 0 ↔ ∃ w ∈ l, (w &&& c).toNat ≠ 0 := by
  induction l with
  | nil => simp [orAll]
  | cons w l ih =>
    simp only [orAll, List.foldr_cons] at ih ⊢
    rw [UInt64.toNat_and, UInt64.toNat_or, Nat.and_or_distrib_right, ← UInt64.toNat_and,
      ← UInt64.toNat_and]
    constructor
    · intro h
      by_cases hw : (w &&& c).toNat = 0
      · rw [hw, Nat.zero_or] at h
        obtain ⟨y, hy, hne⟩ := ih.mp h
        exact ⟨y, List.mem_cons_of_mem w hy, hne⟩
      · exact ⟨w, List.mem_cons_self, hw⟩
    · rintro ⟨y, hy, hne⟩ hz
      rcases Nat.or_eq_zero_iff.mp hz with ⟨h1, h2⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hne h1
      · exact ih.mpr ⟨y, hy, hne⟩ h2

/-! ## One ballot -/

theorem position_empty {w : UInt64} (h : position w = .empty) : w = 0 := by
  unfold position at h
  split at h
  · cases h
  · next h63 =>
    rcases hm : marks w with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · exact marks_nil hm (by simpa using h63)
    · rw [hm] at h; cases h
    · rw [hm] at h; cases h

/-- The slot of a ballot whose examination passes its last position with the union `u` of its
words. -/
def passedSlot (u counted : UInt64) : UInt64 :=
  if u == 0 then 64 else if u &&& counted != 0 then 67 else 65

/-- The words `ws[q]` to `ws[q + m - 1]`. -/
def wordsAt (ws : Array UInt64) (q m : Nat) : List UInt64 :=
  (List.range m).map fun j => ws[q + j]!

theorem wordsAt_succ (ws : Array UInt64) (q m : Nat) :
    wordsAt ws q (m + 1) = ws[q]! :: wordsAt ws (q + 1) m := by
  simp only [wordsAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  congr 1
  omega

/-- `examineAt` from `p` to `e` gives the slot of the examination of the words between, or, when
the examination passes them all, the slot of the union of `seen` and the words. -/
theorem examineAt_eq (ws : Array UInt64) (cont counted : UInt64) (C : List Nat)
    (hC : ∀ i, 1 ≤ i → i ≤ 63 → (i ∈ C ↔ cont.toNat.testBit (i - 1) = true)) :
    ∀ (m : Nat) (p e seen : UInt64), e.toNat = p.toNat + m →
      Program.examineAt ws cont counted e p seen =
        match examine C (wordsAt ws p.toNat m) with
        | some o => UInt64.ofNat (slot o)
        | none => passedSlot (seen ||| orAll (wordsAt ws p.toNat m)) counted := by
  intro m
  induction m with
  | zero =>
    intro p e seen he
    have hpe : e = p := UInt64.toNat_inj.mp (by omega)
    subst hpe
    rw [Program.examineAt, ite_eq_right (by simp)]
    simp only [wordsAt, List.range_zero, List.map_nil, examine, orAll, List.foldr_nil,
      UInt64.or_zero, passedSlot]
  | succ m ih =>
    intro p e seen he
    have hp : p < e := UInt64.lt_iff_toNat_lt.mpr (by omega)
    have hp1 : (p + 1).toNat = p.toNat + 1 := by
      have := UInt64.toNat_lt e
      simp only [UInt64.toNat_add, UInt64.toNat_one]
      omega
    rw [Program.examineAt, ite_eq_left hp]
    dsimp only
    rw [wordsAt_succ, classify_eq]
    simp only [examine, orAll, List.foldr_cons]
    have hrest := ih (p + 1) e (seen ||| ws[p.toNat]!) (by omega)
    rw [hp1] at hrest
    cases hpos : position ws[p.toNat]! with
    | empty =>
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [hrest]
      have hw := position_empty hpos
      split <;> simp [orAll, hw]
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
            rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
            simp
            omega)]
        rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega),
          UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
        simp
      · have hiC : i ∉ C := fun h => hb ((hC i h1 h2).mp h)
        simp only [hb, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, hiC]
        rw [hrest]
        split <;> simp [UInt64.or_assoc, orAll]

theorem examine_valid {C : List Nat} {ps : List UInt64} {o : Outcome} (h : examine C ps = some o) :
    validOutcome o := by
  induction ps with
  | nil => simp [examine] at h
  | cons w ps ih =>
    simp only [examine] at h
    split at h
    · exact ih h
    · cases h; trivial
    · next i hpos =>
      split at h
      · cases h
        obtain ⟨h1, h2, _⟩ := position_single hpos
        exact ⟨h1, h2⟩
      · exact ih h

theorem examine_none {C : List Nat} {ps : List UInt64} (h : examine C ps = none) :
    ∀ w ∈ ps, position w = .empty ∨ ∃ i, i ∉ C ∧ position w = .single i := by
  induction ps with
  | nil => simp
  | cons w ps ih =>
    simp only [examine] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · split at h
      · next hpos => exact Or.inl hpos
      · cases h
      · next i hpos =>
        split at h
        · cases h
        · next hi => exact Or.inr ⟨i, hi, hpos⟩
    · split at h
      · exact ih h x hx
      · cases h
      · split at h
        · cases h
        · exact ih h x hx

theorem interpret_valid (kinds : List Kind) (C : List Nat) (ps : List UInt64) :
    validOutcome (interpret kinds C ps) := by
  unfold interpret
  cases h : examine C ps with
  | none => trivial
  | some o => exact examine_valid h

/-- The slot of a ballot that passes its last position is that of `passedReason`. -/
theorem passedSlot_eq {kinds : List Kind} {counted : UInt64}
    (hK : ∀ i, 1 ≤ i → i ≤ 63 →
      (i ∈ countedSet kinds ↔ counted.toNat.testBit (i - 1) = true))
    {C : List Nat} {ps : List UInt64} (hps : examine C ps = none) :
    passedSlot (orAll ps) counted = UInt64.ofNat (slot (.inactive (passedReason kinds ps))) := by
  have hcls := examine_none hps
  have hzero : (∀ w ∈ ps, w = 0) ↔ ps.all (fun w => position w == .empty) = true := by
    simp only [List.all_eq_true, beq_iff_eq]
    constructor
    · intro h w hw; rw [h w hw]; exact position_zero
    · intro h w hw; exact position_empty (h w hw)
  have hcount : (∃ w ∈ ps, (w &&& counted).toNat ≠ 0) ↔
      ps.any (marksCounted (countedSet kinds)) = true := by
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨w, hw, hne⟩
      refine ⟨w, hw, ?_⟩
      rcases hcls w hw with hpos | ⟨i, _, hpos⟩
      · rw [position_empty hpos] at hne; simp at hne
      · obtain ⟨h1, h2, hwe⟩ := position_single hpos
        have hb : counted.toNat.testBit (i - 1) = true := by
          have := shift_and_ne_zero counted (show i - 1 < 64 by omega)
          rw [← hwe, bne_zero] at this
          rw [← this]
          simpa using hne
        simp only [marksCounted, hpos, decide_eq_true_eq]
        exact (hK i h1 h2).mpr hb
    · rintro ⟨w, hw, hm⟩
      refine ⟨w, hw, ?_⟩
      unfold marksCounted at hm
      split at hm
      · next i hpos =>
        obtain ⟨h1, h2, hwe⟩ := position_single hpos
        have hb := (hK i h1 h2).mp (by simpa using hm)
        have := shift_and_ne_zero counted (show i - 1 < 64 by omega)
        rw [← hwe, bne_zero, hb] at this
        simpa using this
      · cases hm
  unfold passedSlot passedReason
  by_cases hz : orAll ps = 0
  · have hall := hzero.mp (orAll_eq_zero.mp hz)
    simp [hz, hall, slot]
  · have hall : ps.all (fun w => position w == .empty) = false := by
      cases h : ps.all (fun w => position w == .empty)
      · rfl
      · exact absurd (orAll_eq_zero.mpr (hzero.mpr h)) hz
    rw [ite_eq_right (by simpa using hz), hall]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hc : (orAll ps &&& counted).toNat ≠ 0
    · have hany := hcount.mp ((orAll_and_ne_zero counted).mp hc)
      rw [ite_eq_left (by rw [bne_zero]; simpa using hc), ite_eq_left hany]
      rfl
    · have hany : ps.any (marksCounted (countedSet kinds)) = false := by
        cases h : ps.any (marksCounted (countedSet kinds))
        · rfl
        · exact absurd ((orAll_and_ne_zero counted).mpr (hcount.mpr h)) hc
      rw [ite_eq_right (by rw [bne_zero]; simpa using hc), hany]
      rfl

/-- `examineAt` over a ballot's `m` words from `p`, from an empty union, gives the slot of the
ballot's interpretation. -/
theorem examineAt_interpret (ws : Array UInt64) (cont counted : UInt64) (kinds : List Kind)
    (C : List Nat)
    (hC : ∀ i, 1 ≤ i → i ≤ 63 → (i ∈ C ↔ cont.toNat.testBit (i - 1) = true))
    (hK : ∀ i, 1 ≤ i → i ≤ 63 →
      (i ∈ countedSet kinds ↔ counted.toNat.testBit (i - 1) = true))
    (m : Nat) (p e : UInt64) (he : e.toNat = p.toNat + m) :
    Program.examineAt ws cont counted e p 0 =
      UInt64.ofNat (slot (interpret kinds C (wordsAt ws p.toNat m))) := by
  rw [examineAt_eq ws cont counted C hC m p e 0 he]
  unfold interpret
  cases h : examine C (wordsAt ws p.toNat m) with
  | some o => rfl
  | none =>
    simp only [Option.getD_none]
    rw [UInt64.zero_or]
    exact passedSlot_eq hK h

/-! ## The counters of a round -/

/-- Ballot `b` of `k` words from word `q`. -/
def ballotAt (ws : Array UInt64) (q k b : Nat) : List UInt64 := wordsAt ws (q + b * k) k

theorem tallyRound_eq (ws : Array UInt64) (cont counted k N base : UInt64) (kinds : List Kind)
    (C : List Nat)
    (hC : ∀ i, 1 ≤ i → i ≤ 63 → (i ∈ C ↔ cont.toNat.testBit (i - 1) = true))
    (hK : ∀ i, 1 ≤ i → i ≤ 63 →
      (i ∈ countedSet kinds ↔ counted.toNat.testBit (i - 1) = true))
    (hfit : base.toNat + N.toNat * k.toNat < 2 ^ 64) :
    (Program.tallyRound ws cont counted k N base).size = 68 ∧
      ∀ s, s < 68 → (Program.tallyRound ws cont counted k N base)[s]!.toNat =
        (((List.range N.toNat).map fun b => ballotAt ws base.toNat k.toNat b).map
          (interpret kinds C)).countP fun o => slot o = s := by
  unfold Program.tallyRound
  have hinv := LeanExe.Dialect.loop_induction (n := N)
    (init := LeanExe.build 68 fun _ => (0 : UInt64))
    (f := fun b t =>
      let p := base + b * k
      let s := Program.examineAt ws cont counted (p + k) p 0
      t.set! s.toNat (t[s.toNat]! + 1))
    (fun j t => t.size = 68 ∧ ∀ s, s < 68 → t[s]!.toNat =
      (((List.range j).map fun b => ballotAt ws base.toNat k.toNat b).map
        (interpret kinds C)).countP fun o => slot o = s)
    ⟨by simp [LeanExe.Dialect.build_size], fun s hs => by
      rw [LeanExe.Dialect.build_get (by simpa using hs)]
      simp⟩
    (fun j t hj ⟨hsize, hcnt⟩ => by
      have hjk : j * k.toNat ≤ N.toNat * k.toNat := Nat.mul_le_mul_right _ (by omega)
      have hp : (base + UInt64.ofNat j * k).toNat = base.toNat + j * k.toNat := by
        simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (show j < 2 ^ 64 by have := UInt64.toNat_lt N; omega)]
        rw [Nat.mod_eq_of_lt (show j * k.toNat < 2 ^ 64 by omega)]
        omega
      have he : (base + UInt64.ofNat j * k + k).toNat =
          (base + UInt64.ofNat j * k).toNat + k.toNat := by
        rw [UInt64.toNat_add, hp]
        have : base.toNat + j * k.toNat + k.toNat ≤ base.toNat + N.toNat * k.toNat := by
          have : (j + 1) * k.toNat ≤ N.toNat * k.toNat := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.succ_mul] at this
          omega
        omega
      have hs := examineAt_interpret ws cont counted kinds C hC hK k.toNat _ _ he
      dsimp only
      rw [hs, hp]
      set o := interpret kinds C (wordsAt ws (base.toNat + j * k.toNat) k.toNat) with ho
      have hvalid : validOutcome o := interpret_valid _ _ _
      have hslot := slot_lt hvalid
      have hsl : (UInt64.ofNat (slot o)).toNat = slot o :=
        UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
      rw [hsl]
      refine ⟨by simp [hsize], fun s hs' => ?_⟩
      rw [LeanExe.Dialect.get_set _ _ _ _ (by omega), List.range_succ, List.map_append,
        List.map_append, List.countP_append]
      simp only [List.map_cons, List.map_nil, List.countP_cons, List.countP_nil, Nat.zero_add]
      have hle : (((List.range j).map fun b => ballotAt ws base.toNat k.toNat b).map
          (interpret kinds C)).countP (fun o => slot o = s) ≤ j := by
        refine (List.countP_le_length).trans ?_
        simp
      have hlt : j < 2 ^ 64 - 1 := by have := UInt64.toNat_lt N; omega
      by_cases hss : s = slot o
      · subst hss
        simp only [↓reduceIte, ballotAt]
        rw [UInt64.toNat_add, hcnt _ hs', UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
        simp [ballotAt, ← ho]
      · rw [ite_eq_right hss, hcnt s hs']
        simp only [ballotAt]
        have : ¬ (slot o = s) := fun h => hss h.symm
        simp [← ho, this])
  exact hinv

end Demos.Rcv.Refine
