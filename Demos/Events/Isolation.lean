import Demos.Events.Program
import Demos.Screening.Soundness

/-!
Soundness of the isolation for any event.  `Parts` is the real side of an event: two functions
`g₁` and `g₂`, their rate bounds, and their margins, and `Sound` states that the event's
intervals enclose them.  For functions `h₁` and `h₂` within the margins of `g₁` and `g₂` on the
window, `cellTest_zero` states that a cell that the test excludes holds no time at which
`h₁ ≤ 0` and `h₂ ≤ 0`, and `cellTest_whole` that both hold at every time of a cell marked whole.
`isolate_inv` keeps the invariant of the levels, and `finalRuns_spec`, `joinRuns_spec`, and
`output_spec` carry the covering and the labels to the runs of the output.
-/

namespace Demos.Events

open LeanExe.ProofKit LeanExe.Dialect Library.Numerics.Bounds Library.Numerics.Interval
open Library.Numerics.Float64 Demos.Screening
open CodeLib.IEEE64 (value Finite)

/-- The real side of an event: the functions whose signs state its condition, their rate bounds,
and their margins. -/
structure Parts where
  g1 : ℝ → ℝ
  g2 : ℝ → ℝ
  L1 : ℝ
  L2 : ℝ
  W1 : ℝ
  W2 : ℝ

/-- The event's intervals enclose the functions at every time, the rate bounds, and the margins,
and the rate bounds hold. -/
structure Sound (ev : Ev) (M : Parts) : Prop where
  p1 : ∀ m : Float, Encloses (partsAt Trig.invPi Trig.halfPi ev m).1 (M.g1 (val m))
  p2 : ∀ m : Float, Encloses (partsAt Trig.invPi Trig.halfPi ev m).2 (M.g2 (val m))
  l1 : Encloses ev.l1 M.L1
  l2 : Encloses ev.l2 M.L2
  w1 : Encloses ev.w1 M.W1
  w2 : Encloses ev.w2 M.W2
  n1 : 0 ≤ M.L1
  n2 : 0 ≤ M.L2
  lip1 : ∀ t t', |M.g1 t - M.g1 t'| ≤ M.L1 * |t - t'|
  lip2 : ∀ t t', |M.g2 t - M.g2 t'| ≤ M.L2 * |t - t'|

/-- `h₁` and `h₂` lie within the margins of `g₁` and `g₂` at `t`. -/
def Near (M : Parts) (h1 h2 : ℝ → ℝ) (t : ℝ) : Prop :=
  |h1 t - M.g1 t| ≤ M.W1 ∧ |h2 t - M.g2 t| ≤ M.W2

/-- The condition of the functions `h₁` and `h₂` at `t`. -/
def Holds (h1 h2 : ℝ → ℝ) (t : ℝ) : Prop := h1 t ≤ 0 ∧ h2 t ≤ 0

/-! ### The cell test -/

theorem part_pos {g h : ℝ → ℝ} {L W : ℝ} {P Lv Wv : Interval} {m r : Float}
    (hp : Encloses P (g (val m))) (hl : Encloses Lv L) (hw : Encloses Wv W)
    (hlip : ∀ t t', |g t - g t'| ≤ L * |t - t'|) (hL : 0 ≤ L) (hs : P.status = 0)
    (he : (add (mul Lv (point r)) Wv).status = 0) (hlt : (add (mul Lv (point r)) Wv).hi < P.lo)
    {t : ℝ} (ht : |t - val m| ≤ val r) (hn : |h t - g t| ≤ W) : 0 < h t := by
  have ce := encloses_add (encloses_mul hl (encloses_point r)) hw he
  have k := lt_of_hi_lt_lo ce (hp hs) hlt
  have l := abs_le.mp (hlip t (val m))
  have n := abs_le.mp hn
  nlinarith [mul_le_mul_of_nonneg_left ht hL]

theorem part_nonpos {g h : ℝ → ℝ} {L W : ℝ} {P Lv Wv : Interval} {m r : Float}
    (hp : Encloses P (g (val m))) (hl : Encloses Lv L) (hw : Encloses Wv W)
    (hlip : ∀ t t', |g t - g t'| ≤ L * |t - t'|) (hL : 0 ≤ L)
    (hu : (add P (add (mul Lv (point r)) Wv)).status = 0)
    (hle : (add P (add (mul Lv (point r)) Wv)).hi ≤ 0.0)
    {t : ℝ} (ht : |t - val m| ≤ val r) (hn : |h t - g t| ≤ W) : h t ≤ 0 := by
  have cu := encloses_add hp (encloses_add (encloses_mul hl (encloses_point r)) hw) hu
  have k := (le_iff_value cu.2.2.1 lit_zero_finite).mp hle
  rw [show value (0.0 : Float).toBits = 0 from val_zero] at k
  have k' := cu.2.2.2.2
  have l := abs_le.mp (hlip t (val m))
  have n := abs_le.mp hn
  nlinarith [mul_le_mul_of_nonneg_left ht hL]

section Iso

variable {ev : Ev} {M : Parts} {h1 h2 : ℝ → ℝ} {t0 t1 : ℝ}

/-- A cell that the test excludes holds no time at which `h₁` and `h₂` lie within the margins
and the condition holds. -/
theorem cellTest_zero (S : Sound ev M) {s : Span}
    (h : cellTest Trig.invPi Trig.halfPi ev s = 0) {t : ℝ} (hm : Mem1 s t)
    (hn : Near M h1 h2 t) : ¬ Holds h1 h2 t := by
  simp only [cellTest] at h
  have p1 := S.p1 (middle s.lo s.hi)
  have p2 := S.p2 (middle s.lo s.hi)
  generalize middle s.lo s.hi = m at h p1 p2
  generalize partsAt Trig.invPi Trig.halfPi ev m = p at h p1 p2
  split_ifs at h with hA
  all_goals try simp at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hA
  obtain ⟨hr, hA⟩ := hA
  obtain ⟨-, -, hreach⟩ := reach_sound hr
  have hd : |t - val m| ≤ val (reach ⟨0, s.lo, s.hi⟩ m).value := hreach t hm.1 hm.2
  generalize reach ⟨0, s.lo, s.hi⟩ m = r at hA hd
  rintro ⟨H1, H2⟩
  rcases hA with ⟨⟨hs, he⟩, hlt⟩ | ⟨⟨hs, he⟩, hlt⟩
  · exact absurd H1 (not_le.mpr (part_pos p1 S.l1 S.w1 S.lip1 S.n1 hs he hlt hd hn.1))
  · exact absurd H2 (not_le.mpr (part_pos p2 S.l2 S.w2 S.lip2 S.n2 hs he hlt hd hn.2))

/-- The condition holds at every time of a cell that the test marks whole, wherever `h₁` and
`h₂` lie within the margins. -/
theorem cellTest_whole (S : Sound ev M) {s : Span}
    (h : cellTest Trig.invPi Trig.halfPi ev s = 2) {t : ℝ} (hm : Mem1 s t)
    (hn : Near M h1 h2 t) : Holds h1 h2 t := by
  simp only [cellTest] at h
  have p1 := S.p1 (middle s.lo s.hi)
  have p2 := S.p2 (middle s.lo s.hi)
  generalize middle s.lo s.hi = m at h p1 p2
  generalize partsAt Trig.invPi Trig.halfPi ev m = p at h p1 p2
  split_ifs at h with hA hB
  all_goals try simp at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨⟨hr, hu1⟩, hu2⟩, hle1⟩, hle2⟩ := hB
  obtain ⟨-, -, hreach⟩ := reach_sound hr
  have hd : |t - val m| ≤ val (reach ⟨0, s.lo, s.hi⟩ m).value := hreach t hm.1 hm.2
  generalize reach ⟨0, s.lo, s.hi⟩ m = r at hu1 hu2 hle1 hle2 hd
  exact ⟨part_nonpos p1 S.l1 S.w1 S.lip1 S.n1 hu1 hle1 hd hn.1,
    part_nonpos p2 S.l2 S.w2 S.lip2 S.n2 hu2 hle2 hd hn.2⟩

/-! ### The levels -/

/-- The step of `refineCells` for one cell. -/
def cellStep (ev : Ev) (s : Span) (acc : Array Span) : Array Span :=
  if cellTest Trig.invPi Trig.halfPi ev s == 0 then acc
  else
    if (cellTest Trig.invPi Trig.halfPi ev s == 1 && finite (middle s.lo s.hi) &&
        s.lo < middle s.lo s.hi && middle s.lo s.hi < s.hi) = true then
      (acc.push ⟨s.lo, middle s.lo s.hi⟩).push ⟨middle s.lo s.hi, s.hi⟩
    else acc.push s

theorem refineCells_eq (cells : Array Span) :
    refineCells Trig.invPi Trig.halfPi ev cells =
      LeanExe.loop cells.size.toUInt64 #[] fun i acc => cellStep ev cells[i.toNat]! acc :=
  rfl

theorem cellStep_extends (s : Span) : Extends (cellStep ev s) := fun acc => by
  unfold cellStep
  split_ifs
  · exact extends_id acc
  · exact extends_push (extends_push extends_id _) _ acc
  · exact extends_push extends_id _ acc

theorem cellStep_size (s : Span) (acc : Array Span) :
    (cellStep ev s acc).size ≤ acc.size + 2 := by
  unfold cellStep
  split_ifs <;> simp

/-- The cells that a step appends have finite ends in the window when the cell it reads does. -/
theorem cellStep_keep {s : Span} (hs : FiniteSpan s) (hin : Inside t0 t1 s.lo s.hi)
    (acc : Array Span) (j : Nat) (hj0 : acc.size ≤ j) (hj : j < (cellStep ev s acc).size) :
    FiniteSpan (cellStep ev s acc)[j]! ∧
      Inside t0 t1 (cellStep ev s acc)[j]!.lo (cellStep ev s acc)[j]!.hi := by
  unfold cellStep at hj ⊢
  split_ifs at hj ⊢ with h0 h1
  · omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    have fm : Finite (middle s.lo s.hi).toBits :=
      (finite_iff _).mp (decide_eq_true h1.1.1.2)
    have lm := (lt_iff_value hs.1 fm).mp h1.1.2
    have mh := (lt_iff_value fm hs.2).mp h1.2
    simp only [Array.size_push] at hj
    by_cases hj1 : j = acc.size
    · subst hj1
      rw [push_get_lt _ _ (by simp), push_get_size]
      exact ⟨⟨hs.1, fm⟩, hin.1, by show val (middle s.lo s.hi) ≤ t1; linarith [hin.2]⟩
    · have : j = acc.size + 1 := by omega
      subst this
      rw [show acc.size + 1 = (acc.push ⟨s.lo, middle s.lo s.hi⟩).size by simp, push_get_size]
      exact ⟨⟨fm, hs.2⟩, by show t0 ≤ val (middle s.lo s.hi); linarith [hin.1], hin.2⟩
  · simp only [Array.size_push] at hj
    have : j = acc.size := by omega
    subst this
    rw [push_get_size]
    exact ⟨hs, hin⟩

theorem cellStep_cover (S : Sound ev M) {s : Span} {t : ℝ} (hm : Mem1 s t)
    (hn : Near M h1 h2 t) (hc : Holds h1 h2 t) (acc : Array Span) :
    ∃ j < (cellStep ev s acc).size, Mem1 (cellStep ev s acc)[j]! t := by
  unfold cellStep
  by_cases h0 : cellTest Trig.invPi Trig.halfPi ev s = 0
  · exact absurd hc (cellTest_zero S h0 hm hn)
  · simp only [beq_iff_eq, h0, ite_false]
    split_ifs
    · rcases le_total t (val (middle s.lo s.hi)) with h | h
      · exact ⟨acc.size, by simp, by
          rw [push_get_lt _ _ (by simp), push_get_size]; exact ⟨hm.1, h⟩⟩
      · exact ⟨acc.size + 1, by simp, by
          rw [show acc.size + 1 = (acc.push ⟨s.lo, middle s.lo s.hi⟩).size by simp,
            push_get_size]
          exact ⟨h, hm.2⟩⟩
    · exact ⟨acc.size, by simp, by rw [push_get_size]; exact hm⟩

/-- The invariant of the isolation's levels for the window `[t0, t1]`. -/
structure IsoInv (h1 h2 : ℝ → ℝ) (t0 t1 : ℝ) (s : Search) : Prop where
  size : s.cells.size ≤ 1048576
  fin : ∀ j < s.cells.size, FiniteSpan s.cells[j]!
  inside : ∀ j < s.cells.size, Inside t0 t1 s.cells[j]!.lo s.cells[j]!.hi
  cover : ∀ t, t0 ≤ t → t ≤ t1 → Holds h1 h2 t → ∃ j < s.cells.size, Mem1 s.cells[j]! t
  status : s.status = 0 ∨ s.status = 1

theorem isolateLevel_inv (S : Sound ev M) (hN : ∀ t, t0 ≤ t → t ≤ t1 → Near M h1 h2 t)
    {cap : UInt64} (hcap : cap.toNat ≤ 1048576) {s : Search} (h : IsoInv h1 h2 t0 t1 s) :
    IsoInv h1 h2 t0 t1 (isolateLevel Trig.invPi Trig.halfPi ev cap s) := by
  unfold isolateLevel
  by_cases hv : s.status = 0
  · simp only [hv, beq_self_eq_true, ite_true]
    have h64 : s.cells.size < 2 ^ 64 := by have := h.size; omega
    rw [refineCells_eq]
    set next := (LeanExe.loop s.cells.size.toUInt64 #[] fun i acc =>
      cellStep ev s.cells[i.toNat]! acc) with hnext
    have hsize : next.size ≤ 2 * s.cells.size :=
      loop_size_le s.cells h64 _ (fun c acc => cellStep_size c acc)
    have hn64 : next.size < 2 ^ 64 := by have := h.size; omega
    have parts := fun (t : ℝ) => loop_cover s.cells h64 (cellStep ev)
      (fun c => cellStep_extends c) (fun c => FiniteSpan c ∧ Inside t0 t1 c.lo c.hi)
      (fun i hi acc j hj0 hj => cellStep_keep (h.fin i hi) (h.inside i hi) acc j hj0 hj)
      (fun c => Mem1 c t ∧ t0 ≤ t ∧ t ≤ t1 ∧ Holds h1 h2 t) (fun c => Mem1 c t)
      (fun _ _ hin acc => cellStep_cover S hin.1 (hN t hin.2.1 hin.2.2.1) hin.2.2.2 acc)
    by_cases hle : next.size.toUInt64 ≤ cap
    · simp only [hle, ite_true]
      have : next.size ≤ 1048576 := by
        have h1 := size_toUInt64 next hn64
        have h2 : next.size.toUInt64.toNat ≤ cap.toNat := hle
        omega
      refine ⟨this, fun j hj => ((parts 0).1 j hj).1, fun j hj => ((parts 0).1 j hj).2,
        fun t a b c => ?_, Or.inl rfl⟩
      obtain ⟨i, hi, hm⟩ := h.cover t a b c
      exact (parts t).2 ⟨i, hi, hm, a, b, c⟩
    · simp only [hle, ite_false]
      exact ⟨h.size, h.fin, h.inside, h.cover, Or.inr rfl⟩
  · simp only [beq_iff_eq, hv, ite_false]
    exact h

theorem isolate_inv (S : Sound ev M) {lo hi : Float} (f0 : Finite lo.toBits)
    (f1 : Finite hi.toBits) (hN : ∀ t, val lo ≤ t → t ≤ val hi → Near M h1 h2 t)
    {levels cap : UInt64} (hcap : cap.toNat ≤ 1048576) :
    IsoInv h1 h2 (val lo) (val hi) (isolate Trig.invPi Trig.halfPi ev lo hi levels cap) := by
  refine loop_induction (n := levels) (P := fun _ s => IsoInv h1 h2 (val lo) (val hi) s)
    ⟨by simp, fun j hj => ?_, fun j hj => ?_, fun t a b _ => ⟨0, by simp, ?_⟩, Or.inl rfl⟩
    (fun _ s _ hs => isolateLevel_inv S hN hcap hs)
  · have : j = 0 := by simpa using hj
    subst this
    show FiniteSpan ((#[] : Array Span).push ⟨lo, hi⟩)[(#[] : Array Span).size]!
    rw [push_get_size]
    exact ⟨f0, f1⟩
  · have : j = 0 := by simpa using hj
    subst this
    show Inside (val lo) (val hi) ((#[] : Array Span).push ⟨lo, hi⟩)[(#[] : Array Span).size]!.lo
      ((#[] : Array Span).push ⟨lo, hi⟩)[(#[] : Array Span).size]!.hi
    rw [push_get_size]
    exact ⟨le_rfl, le_rfl⟩
  · show Mem1 ((#[] : Array Span).push ⟨lo, hi⟩)[(#[] : Array Span).size]! t
    rw [push_get_size]
    exact ⟨a, b⟩

/-- The status and the levels of the isolation: status 0 after all `levels` levels, or status 1
with fewer levels completed and a next level of more than `cap` cells. -/
theorem isolate_status (ev : Ev) (lo hi : Float) (levels cap : UInt64) :
    ((isolate Trig.invPi Trig.halfPi ev lo hi levels cap).status = 0 ∧
        (isolate Trig.invPi Trig.halfPi ev lo hi levels cap).levels = levels) ∨
      ((isolate Trig.invPi Trig.halfPi ev lo hi levels cap).status = 1 ∧
        (isolate Trig.invPi Trig.halfPi ev lo hi levels cap).levels < levels ∧
        cap < (refineCells Trig.invPi Trig.halfPi ev
          (isolate Trig.invPi Trig.halfPi ev lo hi levels cap).cells).size.toUInt64) := by
  unfold isolate
  have key := loop_induction (n := levels)
    (init := (⟨(#[] : Array Span).push ⟨lo, hi⟩, 0, 0, 0⟩ : Search))
    (f := fun _ s => isolateLevel Trig.invPi Trig.halfPi ev cap s)
    (fun k s => (s.status = 0 ∧ s.levels = UInt64.ofNat k) ∨
      (s.status = 1 ∧ s.levels.toNat < k ∧
        cap < (refineCells Trig.invPi Trig.halfPi ev s.cells).size.toUInt64))
    (Or.inl ⟨rfl, rfl⟩)
    (fun k s hk ih => by
      have hk' : k < 2 ^ 64 := lt_of_lt_of_le hk (UInt64.toNat_lt _).le
      unfold isolateLevel
      rcases ih with ⟨h0, hl⟩ | ⟨h1, hl, hc⟩
      · simp only [h0, beq_self_eq_true, ite_true]
        split_ifs with hle
        · refine Or.inl ⟨rfl, ?_⟩
          show s.levels + 1 = UInt64.ofNat (k + 1)
          rw [hl]
          apply UInt64.toNat_inj.mp
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
          omega
        · refine Or.inr ⟨rfl, ?_, ?_⟩
          · show s.levels.toNat < k + 1
            rw [hl, UInt64.toNat_ofNat']
            omega
          · show cap < (refineCells Trig.invPi Trig.halfPi ev s.cells).size.toUInt64
            rw [UInt64.le_iff_toNat_le] at hle
            rw [UInt64.lt_iff_toNat_lt]
            omega
      · rw [if_neg (by simp [h1])]
        exact Or.inr ⟨h1, by omega, hc⟩)
  have hn : UInt64.ofNat levels.toNat = levels := UInt64.ofNat_toNat
  rcases key with ⟨h0, hl⟩ | ⟨h1, hl, hc⟩
  · exact Or.inl ⟨h0, by rw [hl, hn]⟩
  · exact Or.inr ⟨h1, UInt64.lt_iff_toNat_lt.mpr hl, hc⟩

/-! ### The final pass -/

/-- A run with finite ends in the window `[t0, t1]`, a label 0 or 1, and the condition at every
time of it when its label is 1. -/
structure KeepR (h1 h2 : ℝ → ℝ) (t0 t1 : ℝ) (f : Found) : Prop where
  lo : Finite f.lo.toBits
  hi : Finite f.hi.toBits
  flag : f.certain = 0 ∨ f.certain = 1
  holds : f.certain = 1 → ∀ t, MemF f t → Holds h1 h2 t
  inside : Inside t0 t1 f.lo f.hi

/-- The step of `finalRuns` for one cell. -/
def runStep (ev : Ev) (s : Span) (acc : Array Found) : Array Found :=
  if cellTest Trig.invPi Trig.halfPi ev s == 0 then acc
  else acc.push ⟨s.lo, s.hi, if cellTest Trig.invPi Trig.halfPi ev s == 2 then 1 else 0⟩

theorem finalRuns_eq (cells : Array Span) :
    finalRuns Trig.invPi Trig.halfPi ev cells =
      LeanExe.loop cells.size.toUInt64 #[] fun i acc => runStep ev cells[i.toNat]! acc :=
  rfl

theorem finalRuns_spec (S : Sound ev M) (hN : ∀ t, t0 ≤ t → t ≤ t1 → Near M h1 h2 t)
    {cells : Array Span} (hsize : cells.size ≤ 1048576)
    (hfin : ∀ j < cells.size, FiniteSpan cells[j]!)
    (hin : ∀ j < cells.size, Inside t0 t1 cells[j]!.lo cells[j]!.hi) :
    let r := finalRuns Trig.invPi Trig.halfPi ev cells
    r.size ≤ cells.size ∧ (∀ j < r.size, KeepR h1 h2 t0 t1 r[j]!) ∧
      ∀ t, t0 ≤ t → t ≤ t1 → (∃ i < cells.size, Mem1 cells[i]! t) → Holds h1 h2 t →
        ∃ j < r.size, MemF r[j]! t := by
  intro r
  have h64 : cells.size < 2 ^ 64 := by omega
  have hext : ∀ c, Extends (runStep ev c) := fun c acc => by
    unfold runStep
    split_ifs <;> first | exact extends_id acc | exact extends_push extends_id _ acc
  have hsz : r.size ≤ 1 * cells.size := by
    rw [show r = _ from finalRuns_eq cells]
    exact loop_size_le cells h64 _ (fun c acc => by unfold runStep; split_ifs <;> simp)
  have parts := fun (t : ℝ) => loop_cover cells h64 (runStep ev) hext (KeepR h1 h2 t0 t1)
    (fun i hi acc j hj0 hj => by
      unfold runStep at hj ⊢
      by_cases h0 : cellTest Trig.invPi Trig.halfPi ev cells[i]! = 0
      · simp only [h0, beq_self_eq_true, ite_true] at hj; omega
      · simp only [beq_iff_eq, h0, ite_false, Array.size_push] at hj ⊢
        have : j = acc.size := by omega
        subst this
        rw [push_get_size]
        refine ⟨(hfin i hi).1, (hfin i hi).2, ?_, fun hc u hu => ?_, hin i hi⟩
        · dsimp only
          split_ifs <;> simp
        · dsimp only at hc
          split_ifs at hc with h2
          · have hu' : Mem1 cells[i]! u := hu
            have hw : t0 ≤ u ∧ u ≤ t1 :=
              ⟨(hin i hi).1.trans hu'.1, hu'.2.trans (hin i hi).2⟩
            exact cellTest_whole S h2 hu' (hN u hw.1 hw.2)
          · simp at hc)
    (fun c => Mem1 c t ∧ t0 ≤ t ∧ t ≤ t1 ∧ Holds h1 h2 t) (fun f => MemF f t)
    (fun i _ hc acc => by
      unfold runStep
      by_cases h0 : cellTest Trig.invPi Trig.halfPi ev cells[i]! = 0
      · exact absurd hc.2.2.2 (cellTest_zero S h0 hc.1 (hN t hc.2.1 hc.2.2.1))
      · simp only [beq_iff_eq, h0, ite_false]
        exact ⟨acc.size, by simp, by rw [push_get_size]; exact hc.1⟩)
  refine ⟨by omega, (parts 0).1, fun t a b ⟨i, hi, hm⟩ hc => (parts t).2 ⟨i, hi, hm, a, b, hc⟩⟩

/-! ### The join -/

/-- The invariant of the join after `k` cells, for a time `t`. -/
structure JoinInv (h1 h2 : ℝ → ℝ) (t0 t1 : ℝ) (xs : Array Found) (t : ℝ) (k : Nat)
    (m : Merge) : Prop where
  out : ∀ j < m.out.size, KeepR h1 h2 t0 t1 m.out[j]!
  cur : m.has = true → KeepR h1 h2 t0 t1 m.cur
  size : m.out.size + (if m.has then 1 else 0) ≤ k
  cover : ∀ i < k, MemF xs[i]! t → (∃ j < m.out.size, MemF m.out[j]! t) ∨
    (m.has = true ∧ MemF m.cur t)

/-- The extended run keeps the properties of a run and holds both runs. -/
theorem extend_keep {a b : Found} (ha : KeepR h1 h2 t0 t1 a) (hb : KeepR h1 h2 t0 t1 b)
    (hl : b.certain = a.certain) (h1' : a.lo ≤ b.lo) (h2' : b.lo ≤ a.hi) :
    KeepR h1 h2 t0 t1 ⟨a.lo, fmax a.hi b.hi, a.certain⟩ ∧
      (∀ t, MemF a t → MemF ⟨a.lo, fmax a.hi b.hi, a.certain⟩ t) ∧
      (∀ t, MemF b t → MemF ⟨a.lo, fmax a.hi b.hi, a.certain⟩ t) := by
  obtain ⟨fh, vh⟩ := fmax_value ha.hi hb.hi
  have le1 := (le_iff_value ha.lo hb.lo).mp h1'
  have le2 := (le_iff_value hb.lo ha.hi).mp h2'
  have hv : val (fmax a.hi b.hi) = max (val a.hi) (val b.hi) := vh
  refine ⟨⟨ha.lo, fh, ha.flag, fun hc t ht => ?_, ⟨ha.inside.1, ?_⟩⟩, fun t ht => ?_,
    fun t ht => ?_⟩
  · have ht' : val a.lo ≤ t ∧ t ≤ max (val a.hi) (val b.hi) := by
      rw [← hv]; exact ht
    by_cases hle : t ≤ val a.hi
    · exact ha.holds hc t ⟨ht'.1, hle⟩
    · have hb1 : b.certain = 1 := hl.trans hc
      refine hb.holds hb1 t ⟨by linarith, ?_⟩
      rcases le_total (val a.hi) (val b.hi) with h | h
      · rw [max_eq_right h] at ht'; exact ht'.2
      · rw [max_eq_left h] at ht'; linarith [ht'.2]
  · show val (fmax a.hi b.hi) ≤ t1
    rw [hv]; exact max_le ha.inside.2 hb.inside.2
  · exact ⟨ht.1, by show t ≤ val (fmax a.hi b.hi); rw [hv]; exact le_max_of_le_left ht.2⟩
  · refine ⟨le1.trans ht.1, ?_⟩
    show t ≤ val (fmax a.hi b.hi)
    rw [hv]
    exact le_max_of_le_right ht.2

theorem joinStep_inv {xs : Array Found} {t : ℝ} {k : Nat} (hk : k < xs.size)
    (hx : KeepR h1 h2 t0 t1 xs[k]!) {m : Merge} (h : JoinInv h1 h2 t0 t1 xs t k m) :
    JoinInv h1 h2 t0 t1 xs t (k + 1) (joinStep m xs[k]!) := by
  unfold joinStep
  by_cases hc : (m.has && xs[k]!.certain == m.cur.certain && m.cur.lo ≤ xs[k]!.lo &&
      xs[k]!.lo ≤ m.cur.hi) = true
  · simp only [hc, ite_true]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hh, hl⟩, ha⟩, hb⟩ := hc
    obtain ⟨K, ca, cb⟩ := extend_keep (h.cur hh) hx hl ha hb
    refine ⟨h.out, fun _ => K, by have := h.size; simp only [hh, ite_true] at this ⊢; omega,
      fun i hi hm => ?_⟩
    by_cases hik : i < k
    · rcases h.cover i hik hm with hl' | ⟨-, hr⟩
      · exact Or.inl hl'
      · exact Or.inr ⟨rfl, ca t hr⟩
    · have : i = k := by omega
      subst this
      exact Or.inr ⟨rfl, cb t hm⟩
  · simp only [hc, Bool.false_eq_true, ite_false]
    by_cases hh : m.has = true
    · have hcur := h.cur hh
      simp only [hh, ite_true]
      refine ⟨fun j hj => ?_, fun _ => hx, ?_, fun i hi hm => ?_⟩
      · simp only [Array.size_push] at hj
        by_cases hj1 : j < m.out.size
        · rw [push_get_lt _ _ hj1]; exact h.out j hj1
        · have : j = m.out.size := by omega
          subst this
          rw [push_get_size]; exact hcur
      · have := h.size
        simp only [hh, ite_true, Array.size_push] at this ⊢
        omega
      · by_cases hik : i < k
        · rcases h.cover i hik hm with ⟨j, hj, hmj⟩ | ⟨-, hr⟩
          · exact Or.inl ⟨j, by simp; omega, by rw [push_get_lt _ _ hj]; exact hmj⟩
          · exact Or.inl ⟨m.out.size, by simp, by rw [push_get_size]; exact hr⟩
        · have : i = k := by omega
          subst this
          exact Or.inr ⟨rfl, hm⟩
    · simp only [Bool.not_eq_true] at hh
      simp only [hh, Bool.false_eq_true, ite_false]
      refine ⟨h.out, fun _ => hx, ?_, fun i hi hm => ?_⟩
      · have := h.size
        simp only [hh, Bool.false_eq_true, ite_false, ite_true] at this ⊢
        omega
      · by_cases hik : i < k
        · rcases h.cover i hik hm with hl | ⟨hf, -⟩
          · exact Or.inl hl
          · rw [hh] at hf; exact absurd hf (by decide)
        · have : i = k := by omega
          subst this
          exact Or.inr ⟨rfl, hm⟩

theorem joinRuns_spec {xs : Array Found} (hxs : xs.size ≤ 1048576)
    (hk : ∀ j < xs.size, KeepR h1 h2 t0 t1 xs[j]!) :
    (joinRuns xs).size ≤ xs.size ∧ (∀ j < (joinRuns xs).size, KeepR h1 h2 t0 t1 (joinRuns xs)[j]!) ∧
      ∀ t, (∃ i < xs.size, MemF xs[i]! t) → ∃ j < (joinRuns xs).size, MemF (joinRuns xs)[j]! t := by
  have h64 : xs.size < 2 ^ 64 := by omega
  have hn := size_toUInt64 xs h64
  have inv := fun (t : ℝ) => loop_induction (n := xs.size.toUInt64)
    (init := (⟨#[], ⟨0.0, 0.0, 0⟩, false⟩ : Merge)) (f := fun i m => joinStep m xs[i.toNat]!)
    (fun k m => k ≤ xs.size → JoinInv h1 h2 t0 t1 xs t k m)
    (fun _ => ⟨fun j hj => absurd hj (by simp), fun h => absurd h (by decide), by simp,
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩)
    (fun k m hk' ih _ => by
      rw [hn] at hk'
      have hk'' : (UInt64.ofNat k).toNat = k := by rw [UInt64.toNat_ofNat']; omega
      simp only [hk'']
      exact joinStep_inv hk' (hk k hk') (ih (by omega)))
  simp only [hn] at inv
  unfold joinRuns
  dsimp only
  generalize LeanExe.loop xs.size.toUInt64 (⟨#[], ⟨0.0, 0.0, 0⟩, false⟩ : Merge)
    (fun i m => joinStep m xs[i.toNat]!) = m at inv ⊢
  have I := fun t => inv t le_rfl
  split_ifs with hh
  · refine ⟨?_, fun j hj => ?_, fun t ⟨i, hi, hm⟩ => ?_⟩
    · have := (I 0).size; simp only [hh, ite_true] at this; simp; omega
    · simp only [Array.size_push] at hj
      by_cases hj1 : j < m.out.size
      · rw [push_get_lt _ _ hj1]; exact (I 0).out j hj1
      · have : j = m.out.size := by omega
        subst this
        rw [push_get_size]; exact (I 0).cur hh
    · rcases (I t).cover i hi hm with ⟨j, hj, hmj⟩ | ⟨-, hr⟩
      · exact ⟨j, by simp; omega, by rw [push_get_lt _ _ hj]; exact hmj⟩
      · exact ⟨m.out.size, by simp, by rw [push_get_size]; exact hr⟩
  · refine ⟨?_, (I 0).out, fun t ⟨i, hi, hm⟩ => ?_⟩
    · have := (I 0).size; simp only [hh, Bool.false_eq_true, ite_false] at this; omega
    · rcases (I t).cover i hi hm with hl | ⟨hf, -⟩
      · exact hl
      · exact absurd hf hh

/-! ### The output -/

/-- `t` lies in run `j` of the output: the run with the ends at indices `4 + 3j` and `5 + 3j`,
whose label is at index `6 + 3j`. -/
def InRun (out : Array Float) (j : Nat) (t : ℝ) : Prop :=
  6 + 3 * j < out.size ∧ val out[4 + 3 * j]! ≤ t ∧ t ≤ val out[5 + 3 * j]!

/-- `t` lies in a returned run. -/
def Returned (out : Array Float) (t : ℝ) : Prop := ∃ j, InRun out j t

/-- The output of the isolation and the join: its status, its covering, its labels, and the
window that holds its runs. -/
theorem output_spec (S : Sound ev M) {lo hi : Float} (f0 : Finite lo.toBits)
    (f1 : Finite hi.toBits) (hN : ∀ t, val lo ≤ t → t ≤ val hi → Near M h1 h2 t)
    {levels cap : UInt64} (hcap : cap.toNat ≤ 1048576) :
    let out := outputOf (isolate Trig.invPi Trig.halfPi ev lo hi levels cap)
      (joinRuns (finalRuns Trig.invPi Trig.halfPi ev
        (isolate Trig.invPi Trig.halfPi ev lo hi levels cap).cells))
    (out[0]!.toBits = (0 : UInt64).toFloat.toBits ∨
        out[0]!.toBits = (1 : UInt64).toFloat.toBits) ∧
      (∀ t, val lo ≤ t → t ≤ val hi → Holds h1 h2 t → Returned out t) ∧
      (∀ j, 6 + 3 * j < out.size → out[6 + 3 * j]! = 1.0 →
        ∀ t, val out[4 + 3 * j]! ≤ t → t ≤ val out[5 + 3 * j]! → Holds h1 h2 t) ∧
      ∀ j, 6 + 3 * j < out.size →
        val lo ≤ val out[4 + 3 * j]! ∧ val out[5 + 3 * j]! ≤ val hi := by
  intro out
  have I := isolate_inv S f0 f1 hN (levels := levels) hcap
  simp only [out, outputOf]
  generalize isolate Trig.invPi Trig.halfPi ev lo hi levels cap = s at I ⊢
  obtain ⟨fsz, fkeep, fcov⟩ := finalRuns_spec S hN I.size I.fin I.inside
  generalize finalRuns Trig.invPi Trig.halfPi ev s.cells = found at fsz fkeep fcov ⊢
  obtain ⟨msz, mkeep, mcov⟩ := joinRuns_spec (h1 := h1) (h2 := h2) (t0 := val lo)
    (t1 := val hi) (by have := I.size; omega) fkeep
  generalize joinRuns found = rs at msz mkeep mcov ⊢
  obtain ⟨tsz, tget⟩ := triples_spec rs (by have := I.size; omega)
  generalize hh : (#[s.status.toFloat, rs.size.toUInt64.toFloat,
    (s.tests + s.cells.size.toUInt64).toFloat, s.levels.toFloat] : Array Float) = head
  have hs : head.size = 4 := by rw [← hh]; rfl
  have h0 : head[0]! = s.status.toFloat := by rw [← hh]; rfl
  have osz : (head ++ triples rs).size = 4 + 3 * rs.size := by simp [hs, tsz]
  have lo' : ∀ j < rs.size, (head ++ triples rs)[4 + 3 * j]! = rs[j]!.lo := fun j hj => by
    rw [← hs, append_get_right _ _ _ (by omega)]; exact (tget j hj).1
  have hi' : ∀ j < rs.size, (head ++ triples rs)[5 + 3 * j]! = rs[j]!.hi := fun j hj => by
    rw [show 5 + 3 * j = head.size + (3 * j + 1) by omega, append_get_right _ _ _ (by omega)]
    exact (tget j hj).2.1
  have ce : ∀ j < rs.size, (head ++ triples rs)[6 + 3 * j]! = rs[j]!.certain.toFloat :=
    fun j hj => by
      rw [show 6 + 3 * j = head.size + (3 * j + 2) by omega, append_get_right _ _ _ (by omega)]
      exact (tget j hj).2.2
  refine ⟨?_, fun t a b c => ?_, fun j hj hf t ha hb => ?_, fun j hj => ?_⟩
  · rw [append_get_left _ _ 0 (by omega), h0]
    rcases I.status with h | h <;> rw [h] <;> simp
  · obtain ⟨i, hi'', hm⟩ := I.cover t a b c
    obtain ⟨k, hk, hmk⟩ := fcov t a b ⟨i, hi'', hm⟩ c
    obtain ⟨j, hj, hmj⟩ := mcov t ⟨k, hk, hmk⟩
    exact ⟨j, by omega, by rw [lo' j hj]; exact hmj.1, by rw [hi' j hj]; exact hmj.2⟩
  · have hj' : j < rs.size := by omega
    have K := mkeep j hj'
    rw [ce j hj'] at hf
    have h1 : rs[j]!.certain = 1 := by
      rcases K.flag with h | h
      · rw [h] at hf; exact absurd (congrArg Float.toBits hf) (by decide +kernel)
      · exact h
    rw [lo' j hj'] at ha
    rw [hi' j hj'] at hb
    exact K.holds h1 t ⟨ha, hb⟩
  · have hj' : j < rs.size := by omega
    have K := mkeep j hj'
    exact ⟨by rw [lo' j hj']; exact K.inside.1, by rw [hi' j hj']; exact K.inside.2⟩

end Iso

end Demos.Events
