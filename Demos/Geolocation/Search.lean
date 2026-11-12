import Demos.Geolocation.Program
import Demos.Screening.Soundness

/-!
Soundness of the search for any box test with two facts (`TestSound`): a box whose test gives 0
holds no point of a target set, and a box whose test gives 2 has a property `Good`.  `level_inv`
keeps the invariant of the levels, `search_inv` and `search_status` state it after the levels,
and `finalBoxes_spec` and `output_spec` carry the covering, the property of the boxes labeled 1,
and the region to the boxes of the output.
-/

namespace Demos.Geolocation

open LeanExe.ProofKit LeanExe.Dialect Library.Numerics.Bounds Library.Numerics.Interval
open Library.Numerics.Float64
open Demos.Screening (val middle Extends extends_id extends_push loop_cover loop_size_le
  append_get_left append_get_right)
open CodeLib.IEEE64 (value Finite)

/-- The point `(φ, λ, h)` lies in the box. -/
def InBox (b : Box) (φ lam h : ℝ) : Prop :=
  val b.plo ≤ φ ∧ φ ≤ val b.phi ∧ val b.llo ≤ lam ∧ lam ≤ val b.lhi ∧
    val b.hlo ≤ h ∧ h ≤ val b.hhi

/-- The ends of the box are finite. -/
def FiniteBox (b : Box) : Prop :=
  Finite b.plo.toBits ∧ Finite b.phi.toBits ∧ Finite b.llo.toBits ∧ Finite b.lhi.toBits ∧
    Finite b.hlo.toBits ∧ Finite b.hhi.toBits

/-- The box `b` lies in the box `R`. -/
def Within (R b : Box) : Prop :=
  val R.plo ≤ val b.plo ∧ val b.phi ≤ val R.phi ∧ val R.llo ≤ val b.llo ∧
    val b.lhi ≤ val R.lhi ∧ val R.hlo ≤ val b.hlo ∧ val b.hhi ≤ val R.hhi

/-- A box of the search: finite ends in the region `R`, a mark 0, 1, or 2, the property `Good`
for mark 2, and no split for mark 1. -/
structure Keep (R : Box) (Good : Box → Prop) (r : Float) (b : Box) : Prop where
  fin : FiniteBox b
  within : Within R b
  mark : b.mark = 0 ∨ b.mark = 1 ∨ b.mark = 2
  good : b.mark = 2 → Good b
  unsplit : b.mark = 1 → splits Trig.invPi Trig.halfPi r b = false

theorem keep_fresh {R : Box} {Good : Box → Prop} {r : Float} {b : Box} (hf : FiniteBox b)
    (hw : Within R b) (hm : b.mark = 0) : Keep R Good r b :=
  ⟨hf, hw, Or.inl hm, fun h => by rw [hm] at h; exact absurd h (by decide),
    fun h => by rw [hm] at h; exact absurd h (by decide)⟩

/-! ### Splitting -/

theorem sideLo_finite {b : Box} (hb : FiniteBox b) (s : UInt64) : Finite (sideLo b s).toBits := by
  unfold sideLo
  split_ifs
  · exact hb.1
  · exact hb.2.2.1
  · exact hb.2.2.2.2.1

theorem sideHi_finite {b : Box} (hb : FiniteBox b) (s : UInt64) : Finite (sideHi b s).toBits := by
  unfold sideHi
  split_ifs
  · exact hb.2.1
  · exact hb.2.2.2.1
  · exact hb.2.2.2.2.2

/-- The two halves of a box at a finite `md` strictly inside a side are boxes of the search, and
every point of the box lies in one of them. -/
theorem halves {R : Box} {Good : Box → Prop} {r : Float} {b : Box} (hb : FiniteBox b)
    (hw : Within R b) {s : UInt64} {md : Float} (fm : Finite md.toBits)
    (l1 : val (sideLo b s) < val md) (l2 : val md < val (sideHi b s)) :
    Keep R Good r (lowerHalf b s md) ∧ Keep R Good r (upperHalf b s md) ∧
      ∀ φ lam h, InBox b φ lam h → InBox (lowerHalf b s md) φ lam h ∨
        InBox (upperHalf b s md) φ lam h := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hb
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hw
  unfold sideLo at l1
  unfold sideHi at l2
  unfold lowerHalf upperHalf
  split_ifs at l1 l2 ⊢
  · refine ⟨keep_fresh ⟨f1, fm, f3, f4, f5, f6⟩
        ⟨w1, by dsimp only; linarith, w3, w4, w5, w6⟩ rfl,
      keep_fresh ⟨fm, f2, f3, f4, f5, f6⟩ ⟨by dsimp only; linarith, w2, w3, w4, w5, w6⟩ rfl,
      fun φ lam h ⟨a1, a2, a3, a4, a5, a6⟩ => ?_⟩
    rcases le_total φ (val md) with e | e
    · exact Or.inl ⟨a1, e, a3, a4, a5, a6⟩
    · exact Or.inr ⟨e, a2, a3, a4, a5, a6⟩
  · refine ⟨keep_fresh ⟨f1, f2, f3, fm, f5, f6⟩
        ⟨w1, w2, w3, by dsimp only; linarith, w5, w6⟩ rfl,
      keep_fresh ⟨f1, f2, fm, f4, f5, f6⟩ ⟨w1, w2, by dsimp only; linarith, w4, w5, w6⟩ rfl,
      fun φ lam h ⟨a1, a2, a3, a4, a5, a6⟩ => ?_⟩
    rcases le_total lam (val md) with e | e
    · exact Or.inl ⟨a1, a2, a3, e, a5, a6⟩
    · exact Or.inr ⟨a1, a2, e, a4, a5, a6⟩
  · refine ⟨keep_fresh ⟨f1, f2, f3, f4, f5, fm⟩
        ⟨w1, w2, w3, w4, w5, by dsimp only; linarith⟩ rfl,
      keep_fresh ⟨f1, f2, f3, f4, fm, f6⟩ ⟨w1, w2, w3, w4, by dsimp only; linarith, w6⟩ rfl,
      fun φ lam h ⟨a1, a2, a3, a4, a5, a6⟩ => ?_⟩
    rcases le_total h (val md) with e | e
    · exact Or.inl ⟨a1, a2, a3, a4, a5, e⟩
    · exact Or.inr ⟨a1, a2, a3, a4, e, a6⟩

/-- The facts of `splits`: a finite middle strictly inside the longest side. -/
theorem splits_facts {r : Float} {b : Box} (hb : FiniteBox b)
    (hs : splits Trig.invPi Trig.halfPi r b = true) :
    let s := (longest Trig.invPi Trig.halfPi b).1
    let md := middle (sideLo b s) (sideHi b s)
    Finite md.toBits ∧ val (sideLo b s) < val md ∧ val md < val (sideHi b s) := by
  intro s md
  simp only [splits, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨-, hf⟩, h1⟩, h2⟩ := hs
  have fm : Finite md.toBits := (finite_iff _).mp hf
  exact ⟨fm, (lt_iff_value (sideLo_finite hb _) fm).mp (of_decide_eq_true h1),
    (lt_iff_value fm (sideHi_finite hb _)).mp (of_decide_eq_true h2)⟩

/-! ### The levels -/

section Search

variable {rx : Array Interval} {fq : Interval} {xs : Array Float} {base m : UInt64} {r : Float}
variable {R : Box} {Target : ℝ → ℝ → ℝ → Prop} {Good : Box → Prop}

/-- The two facts of the box test for a target set and a property of boxes that depends only on
the ends of a box. -/
structure TestSound (rx : Array Interval) (fq : Interval) (xs : Array Float) (base m : UInt64)
    (Target : ℝ → ℝ → ℝ → Prop) (Good : Box → Prop) : Prop where
  zero : ∀ b, boxTest Trig.invPi Trig.halfPi rx fq xs base m b = 0 →
    ∀ φ lam h, InBox b φ lam h → ¬ Target φ lam h
  two : ∀ b, boxTest Trig.invPi Trig.halfPi rx fq xs base m b = 2 → Good b
  ends : ∀ b k, Good b → Good { b with mark := k }

theorem boxTest_cases (b : Box) :
    boxTest Trig.invPi Trig.halfPi rx fq xs base m b = 0 ∨
      boxTest Trig.invPi Trig.halfPi rx fq xs base m b = 1 ∨
      boxTest Trig.invPi Trig.halfPi rx fq xs base m b = 2 := by
  unfold boxTest
  dsimp only
  split_ifs <;> simp

theorem refine_eq (boxes : Array Box) :
    refine Trig.invPi Trig.halfPi rx fq xs base m r boxes =
      LeanExe.loop boxes.size.toUInt64 #[] fun i acc =>
        boxStep Trig.invPi Trig.halfPi rx fq xs base m r boxes[i.toNat]! acc :=
  rfl

theorem boxStep_extends (b : Box) :
    Extends (boxStep Trig.invPi Trig.halfPi rx fq xs base m r b) := fun acc => by
  unfold boxStep
  dsimp only
  split_ifs
  · exact extends_id acc
  · exact extends_push extends_id _ acc
  · exact extends_push (extends_push extends_id _) _ acc
  · exact extends_push extends_id _ acc
  · exact extends_push extends_id _ acc

theorem boxStep_size (b : Box) (acc : Array Box) :
    (boxStep Trig.invPi Trig.halfPi rx fq xs base m r b acc).size ≤ acc.size + 2 := by
  unfold boxStep
  dsimp only
  split_ifs <;> simp

theorem push2_fst {α : Type} [Inhabited α] (acc : Array α) (a b : α) :
    ((acc.push a).push b)[acc.size]! = a := by
  rw [push_get_lt _ _ (by simp), push_get_size]

theorem push2_snd {α : Type} [Inhabited α] (acc : Array α) (a b : α) :
    ((acc.push a).push b)[acc.size + 1]! = b := by
  rw [show acc.size + 1 = (acc.push a).size by simp, push_get_size]

theorem splits_mark (r : Float) (b : Box) (k : UInt64) :
    splits Trig.invPi Trig.halfPi r { b with mark := k } =
      splits Trig.invPi Trig.halfPi r b := rfl

/-- The boxes that a step appends are boxes of the search when the box it reads is one. -/
theorem boxStep_keep (T : TestSound rx fq xs base m Target Good) {b : Box}
    (hb : Keep R Good r b) (acc : Array Box) (j : Nat) (hj0 : acc.size ≤ j)
    (hj : j < (boxStep Trig.invPi Trig.halfPi rx fq xs base m r b acc).size) :
    Keep R Good r (boxStep Trig.invPi Trig.halfPi rx fq xs base m r b acc)[j]! := by
  unfold boxStep at hj ⊢
  dsimp only at hj ⊢
  split_ifs at hj ⊢ with h0 t0 t2 hs
  · omega
  · simp only [Array.size_push] at hj
    have : j = acc.size := by omega
    subst this
    rw [push_get_size]
    exact ⟨hb.fin, hb.within, Or.inr (Or.inr rfl),
      fun _ => T.ends b 2 (T.two b (beq_iff_eq.mp t2)),
      fun h => absurd (show (2 : UInt64) = 1 from h) (by decide)⟩
  · obtain ⟨fm, l1, l2⟩ := splits_facts hb.fin hs
    obtain ⟨k1, k2, -⟩ := halves (Good := Good) (r := r) hb.fin hb.within fm l1 l2
    simp only [Array.size_push] at hj
    by_cases hj1 : j = acc.size
    · subst hj1
      rw [push2_fst]
      exact k1
    · have : j = acc.size + 1 := by omega
      subst this
      rw [push2_snd]
      exact k2
  · simp only [Array.size_push] at hj
    have : j = acc.size := by omega
    subst this
    rw [push_get_size]
    have hs' : splits Trig.invPi Trig.halfPi r b = false := by simpa using hs
    exact ⟨hb.fin, hb.within, Or.inr (Or.inl rfl),
      fun h => absurd (show (1 : UInt64) = 2 from h) (by decide),
      fun _ => (splits_mark r b 1).trans hs'⟩
  · simp only [Array.size_push] at hj
    have : j = acc.size := by omega
    subst this
    rw [push_get_size]
    exact hb

/-- A point of the target set in the box that a step reads lies in a box that it appends. -/
theorem boxStep_cover (T : TestSound rx fq xs base m Target Good) {b : Box}
    (hb : Keep R Good r b) {φ lam h : ℝ} (hm : InBox b φ lam h) (ht : Target φ lam h)
    (acc : Array Box) :
    ∃ j < (boxStep Trig.invPi Trig.halfPi rx fq xs base m r b acc).size,
      InBox (boxStep Trig.invPi Trig.halfPi rx fq xs base m r b acc)[j]! φ lam h := by
  unfold boxStep
  dsimp only
  split_ifs with h0 t0 t2 hs
  · exact absurd ht (T.zero b (beq_iff_eq.mp t0) φ lam h hm)
  · exact ⟨acc.size, by simp, by rw [push_get_size]; exact hm⟩
  · obtain ⟨fm, l1, l2⟩ := splits_facts hb.fin hs
    obtain ⟨-, -, hc⟩ := halves (Good := Good) (R := R) (r := r) hb.fin hb.within fm l1 l2
    rcases hc φ lam h hm with e | e
    · exact ⟨acc.size, by simp, by rw [push2_fst]; exact e⟩
    · exact ⟨acc.size + 1, by simp, by rw [push2_snd]; exact e⟩
  · exact ⟨acc.size, by simp, by rw [push_get_size]; exact hm⟩
  · exact ⟨acc.size, by simp, by rw [push_get_size]; exact hm⟩

/-- The invariant of the levels for the region `R` and at most `cap` boxes. -/
structure Inv (R : Box) (Target : ℝ → ℝ → ℝ → Prop) (Good : Box → Prop) (r : Float)
    (cap : Nat) (s : Search) : Prop where
  size : s.boxes.size ≤ cap
  keep : ∀ j < s.boxes.size, Keep R Good r s.boxes[j]!
  cover : ∀ φ lam h, InBox R φ lam h → Target φ lam h →
    ∃ j < s.boxes.size, InBox s.boxes[j]! φ lam h

theorem level_inv (T : TestSound rx fq xs base m Target Good) {cap : UInt64}
    (hcap : cap.toNat ≤ 65536) {s : Search} (h : Inv R Target Good r cap.toNat s) :
    Inv R Target Good r cap.toNat (level Trig.invPi Trig.halfPi rx fq xs base m r cap s) := by
  unfold level
  by_cases hv : s.status = 2
  · simp only [hv, beq_self_eq_true, ite_true]
    have h64 : s.boxes.size < 2 ^ 64 := by have := h.size; omega
    rw [refine_eq]
    set next := (LeanExe.loop s.boxes.size.toUInt64 #[] fun i acc =>
      boxStep Trig.invPi Trig.halfPi rx fq xs base m r s.boxes[i.toNat]! acc) with hnext
    have hsize : next.size ≤ 2 * s.boxes.size :=
      loop_size_le s.boxes h64 _ (fun c acc => boxStep_size c acc)
    have hn64 : next.size < 2 ^ 64 := by have := h.size; omega
    have parts := fun (φ lam hh : ℝ) => loop_cover s.boxes h64
      (boxStep Trig.invPi Trig.halfPi rx fq xs base m r) (fun c => boxStep_extends c)
      (Keep R Good r) (fun i hi acc j hj0 hj => boxStep_keep T (h.keep i hi) acc j hj0 hj)
      (fun c => Keep R Good r c ∧ InBox c φ lam hh ∧ Target φ lam hh)
      (fun c => InBox c φ lam hh)
      (fun _ _ hin acc => boxStep_cover T hin.1 hin.2.1 hin.2.2 acc)
    by_cases hle : cap < next.size.toUInt64
    · simp only [hle, ite_true]
      exact ⟨h.size, h.keep, h.cover⟩
    · simp only [hle, ite_false]
      have hle' : next.size ≤ cap.toNat := by
        have h1 := LeanExe.Dialect.size_toUInt64 next hn64
        have h2 : ¬ cap.toNat < next.size.toUInt64.toNat :=
          fun c => hle (UInt64.lt_iff_toNat_lt.mpr c)
        omega
      have I : Inv R Target Good r cap.toNat ⟨next, 0, 0, 0⟩ :=
        ⟨hle', fun j hj => (parts 0 0 0).1 j hj, fun φ lam hh hr ht => by
          obtain ⟨i, hi, hm⟩ := h.cover φ lam hh hr ht
          exact (parts φ lam hh).2 ⟨i, hi, h.keep i hi, hm, ht⟩⟩
      split_ifs
      · exact ⟨I.size, I.keep, I.cover⟩
      · exact ⟨I.size, I.keep, I.cover⟩
  · simp only [beq_iff_eq, hv, ite_false]
    exact h

theorem search_inv (T : TestSound rx fq xs base m Target Good) {cap levels : UInt64}
    (hcap1 : 1 ≤ cap.toNat) (hcap : cap.toNat ≤ 65536) (hR : FiniteBox R) (hR0 : R.mark = 0) :
    Inv R Target Good r cap.toNat
      (search Trig.invPi Trig.halfPi rx fq xs base m r R levels cap) := by
  refine loop_induction (n := levels) (P := fun _ s => Inv R Target Good r cap.toNat s)
    ⟨by simpa using hcap1, fun j hj => ?_, fun φ lam hh hr _ => ⟨0, by simp, ?_⟩⟩
    (fun _ s _ hs => level_inv T hcap hs)
  · have : j = 0 := by simpa using hj
    subst this
    show Keep R Good r ((#[] : Array Box).push R)[(#[] : Array Box).size]!
    rw [push_get_size]
    exact keep_fresh hR ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩ hR0
  · show InBox ((#[] : Array Box).push R)[(#[] : Array Box).size]! φ lam hh
    rw [push_get_size]
    exact hr

/-- The untested boxes are counted: when the count is 0, every box has been tested. -/
theorem fresh_zero {boxes : Array Box} (h64 : boxes.size < 2 ^ 64) (h : fresh boxes = 0) :
    ∀ j < boxes.size, boxes[j]!.mark ≠ 0 := by
  have hn := LeanExe.Dialect.size_toUInt64 boxes h64
  have key := loop_induction (n := boxes.size.toUInt64) (init := (0 : UInt64))
    (f := fun i k => if boxes[i.toNat]!.mark == 0 then k + 1 else k)
    (fun k c => c.toNat ≤ k ∧ (c = 0 → ∀ j < k, boxes[j]!.mark ≠ 0))
    ⟨by simp, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩
    (fun k c hk ⟨hle, hz⟩ => by
      rw [hn] at hk
      have hk' : (UInt64.ofNat k).toNat = k := by rw [UInt64.toNat_ofNat']; omega
      simp only [hk']
      by_cases hm : boxes[k]!.mark = 0
      · simp only [hm, beq_self_eq_true, ite_true]
        have hc1 : (c + 1).toNat = c.toNat + 1 := by
          rw [UInt64.toNat_add]
          simp only [UInt64.reduceToNat]
          exact Nat.mod_eq_of_lt (by omega)
        refine ⟨by omega, fun hc => ?_⟩
        exfalso
        have := congrArg UInt64.toNat hc
        simp only [UInt64.reduceToNat] at this
        omega
      · simp only [beq_iff_eq, hm, ite_false]
        refine ⟨by omega, fun hc j hj => ?_⟩
        by_cases hjk : j < k
        · exact hz hc j hjk
        · have : j = k := by omega
          subst this; exact hm)
  rw [hn] at key
  exact key.2 h

/-- The status and the levels of the search: status 2 after all `levels` levels, status 0 with
no untested box after at most `levels` levels, or status 1 with fewer levels. -/
theorem search_status (R : Box) (cap levels : UInt64) :
    let s := search Trig.invPi Trig.halfPi rx fq xs base m r R levels cap
    (s.status = 2 ∧ s.levels = levels) ∨
      (s.status = 0 ∧ s.levels ≤ levels ∧ fresh s.boxes = 0) ∨
      (s.status = 1 ∧ s.levels < levels) := by
  intro s
  have key := loop_induction (n := levels)
    (init := (⟨(#[] : Array Box).push R, 2, 0, 0⟩ : Search))
    (f := fun _ s => level Trig.invPi Trig.halfPi rx fq xs base m r cap s)
    (fun k s => (s.status = 2 ∧ s.levels = UInt64.ofNat k) ∨
      (s.status = 0 ∧ s.levels.toNat ≤ k ∧ fresh s.boxes = 0) ∨
      (s.status = 1 ∧ s.levels.toNat < k))
    (Or.inl ⟨rfl, rfl⟩)
    (fun k s hk ih => by
      have hk' : k + 1 < 2 ^ 64 := by
        have := UInt64.toNat_lt levels; omega
      unfold level
      rcases ih with ⟨h2, hl⟩ | ⟨h0, hl, hf⟩ | ⟨h1, hl⟩
      · simp only [h2, beq_self_eq_true, ite_true]
        have hlk : s.levels.toNat = k := by rw [hl, UInt64.toNat_ofNat']; omega
        split_ifs with hc hf
        · exact Or.inr (Or.inr ⟨rfl, by show s.levels.toNat < k + 1; omega⟩)
        · refine Or.inr (Or.inl ⟨rfl, ?_, by simpa using hf⟩)
          show (s.levels + 1).toNat ≤ k + 1
          rw [UInt64.toNat_add]; simp; omega
        · refine Or.inl ⟨rfl, ?_⟩
          show s.levels + 1 = UInt64.ofNat (k + 1)
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add, UInt64.toNat_ofNat']
          simp only [UInt64.reduceToNat]
          omega
      · rw [if_neg (by simp [h0])]
        exact Or.inr (Or.inl ⟨h0, by omega, hf⟩)
      · rw [if_neg (by simp [h1])]
        exact Or.inr (Or.inr ⟨h1, by omega⟩))
  have hn : UInt64.ofNat levels.toNat = levels := UInt64.ofNat_toNat
  rcases key with ⟨h2, hl⟩ | ⟨h0, hl, hf⟩ | ⟨h1, hl⟩
  · exact Or.inl ⟨h2, hl.trans hn⟩
  · exact Or.inr (Or.inl ⟨h0, UInt64.le_iff_toNat_le.mpr hl, hf⟩)
  · exact Or.inr (Or.inr ⟨h1, UInt64.lt_iff_toNat_lt.mpr hl⟩)

/-! ### The final pass -/

/-- A box of the output: finite ends in the region `R`, a mark 1 or 2, the property `Good` for
mark 2, and no split for mark 1 when `U` holds. -/
structure KeepF (R : Box) (Good : Box → Prop) (r : Float) (U : Prop) (b : Box) : Prop where
  fin : FiniteBox b
  within : Within R b
  mark : b.mark = 1 ∨ b.mark = 2
  good : b.mark = 2 → Good b
  unsplit : U → b.mark = 1 → splits Trig.invPi Trig.halfPi r b = false

theorem finalBoxes_eq (boxes : Array Box) :
    finalBoxes Trig.invPi Trig.halfPi rx fq xs base m boxes =
      LeanExe.loop boxes.size.toUInt64 #[] fun i acc =>
        finalStep Trig.invPi Trig.halfPi rx fq xs base m boxes[i.toNat]! acc :=
  rfl

theorem finalBoxes_spec (T : TestSound rx fq xs base m Target Good) {boxes : Array Box}
    (hsize : boxes.size ≤ 65536) (hk : ∀ j < boxes.size, Keep R Good r boxes[j]!) :
    let out := finalBoxes Trig.invPi Trig.halfPi rx fq xs base m boxes
    out.size ≤ boxes.size ∧
      (∀ j < out.size, KeepF R Good r (∀ i < boxes.size, boxes[i]!.mark ≠ 0) out[j]!) ∧
      ∀ φ lam h, (∃ i < boxes.size, InBox boxes[i]! φ lam h) → Target φ lam h →
        ∃ j < out.size, InBox out[j]! φ lam h := by
  intro out
  have h64 : boxes.size < 2 ^ 64 := by omega
  have hext : ∀ c, Extends (finalStep Trig.invPi Trig.halfPi rx fq xs base m c) := fun c acc => by
    unfold finalStep
    dsimp only
    split_ifs <;> first | exact extends_id acc | exact extends_push extends_id _ acc
  have hsz : out.size ≤ 1 * boxes.size := by
    rw [show out = _ from finalBoxes_eq boxes]
    exact loop_size_le boxes h64 _ (fun c acc => by
      unfold finalStep; dsimp only; split_ifs <;> simp)
  have parts := fun (φ lam hh : ℝ) => loop_cover boxes h64
    (finalStep Trig.invPi Trig.halfPi rx fq xs base m) hext
    (KeepF R Good r (∀ i < boxes.size, boxes[i]!.mark ≠ 0))
    (fun i hi acc j hj0 hj => by
      have K := hk i hi
      unfold finalStep at hj ⊢
      by_cases h0 : boxes[i]!.mark = 0
      · simp only [h0, beq_self_eq_true, ite_true] at hj ⊢
        by_cases t0 : boxTest Trig.invPi Trig.halfPi rx fq xs base m boxes[i]! = 0
        · simp only [t0, beq_self_eq_true, ite_true] at hj; omega
        · simp only [beq_iff_eq, t0, ite_false, Array.size_push] at hj ⊢
          have : j = acc.size := by omega
          subst this
          rw [push_get_size]
          have tc := boxTest_cases (rx := rx) (fq := fq) (xs := xs) (base := base) (m := m)
            boxes[i]!
          refine ⟨K.fin, K.within, ?_, fun h2 => ?_, fun hU _ => absurd h0 (hU i hi)⟩
          · rcases tc with e | e | e
            · exact absurd e t0
            · exact Or.inl e
            · exact Or.inr e
          · exact T.ends _ _ (T.two _ h2)
      · simp only [beq_iff_eq, h0, ite_false, Array.size_push] at hj ⊢
        have : j = acc.size := by omega
        subst this
        rw [push_get_size]
        refine ⟨K.fin, K.within, ?_, K.good, fun _ => K.unsplit⟩
        rcases K.mark with e | e | e
        · exact absurd e h0
        · exact Or.inl e
        · exact Or.inr e)
    (fun c => InBox c φ lam hh ∧ Target φ lam hh) (fun c => InBox c φ lam hh)
    (fun i _ hc acc => by
      unfold finalStep
      by_cases h0 : boxes[i]!.mark = 0
      · simp only [h0, beq_self_eq_true, ite_true]
        by_cases t0 : boxTest Trig.invPi Trig.halfPi rx fq xs base m boxes[i]! = 0
        · exact absurd hc.2 (T.zero _ t0 φ lam hh hc.1)
        · simp only [beq_iff_eq, t0, ite_false]
          exact ⟨acc.size, by simp, by rw [push_get_size]; exact hc.1⟩
      · simp only [beq_iff_eq, h0, ite_false]
        exact ⟨acc.size, by simp, by rw [push_get_size]; exact hc.1⟩)
  refine ⟨by omega, (parts 0 0 0).1, fun φ lam hh ⟨i, hi, hm⟩ ht =>
    (parts φ lam hh).2 ⟨i, hi, hm, ht⟩⟩

end Search

/-! ### The output -/

theorem uint_div_mod7 (q : Nat) (hq : q < 2 ^ 64) :
    ((UInt64.ofNat q) / 7).toNat = q / 7 ∧ ((UInt64.ofNat q) % 7).toNat = q % 7 := by
  have h : (UInt64.ofNat q).toNat = q := by rw [UInt64.toNat_ofNat']; omega
  exact ⟨by rw [UInt64.toNat_div, h]; rfl, by rw [UInt64.toNat_mod, h]; rfl⟩

/-- The value of `sevens` at index `7 j + c`. -/
theorem sevens_get (bs : Array Box) (h : bs.size ≤ 65536) {j c : Nat} (hj : j < bs.size)
    (hc : c < 7) :
    (sevens bs)[7 * j + c]! =
      (if c = 0 then bs[j]!.plo else if c = 1 then bs[j]!.phi else if c = 2 then bs[j]!.llo
      else if c = 3 then bs[j]!.lhi else if c = 4 then bs[j]!.hlo else if c = 5 then bs[j]!.hhi
      else if bs[j]!.mark == 2 then 1.0 else 0.0) := by
  have hn : (7 * bs.size.toUInt64).toNat = 7 * bs.size := by
    rw [UInt64.toNat_mul, LeanExe.Dialect.size_toUInt64 bs (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  unfold sevens
  rw [build_get (by rw [hn]; omega)]
  obtain ⟨d, md⟩ := uint_div_mod7 (7 * j + c) (by omega)
  have hd : (UInt64.ofNat (7 * j + c) / 7).toNat = j := by rw [d]; omega
  have hm : UInt64.ofNat (7 * j + c) % 7 = UInt64.ofNat c := by
    apply UInt64.toNat_inj.mp
    rw [md, UInt64.toNat_ofNat']
    omega
  simp only [hd, hm]
  interval_cases c <;> rfl

theorem sevens_box (bs : Array Box) (h : bs.size ≤ 65536) {j : Nat} (hj : j < bs.size) :
    (sevens bs)[7 * j]! = bs[j]!.plo ∧ (sevens bs)[7 * j + 1]! = bs[j]!.phi ∧
      (sevens bs)[7 * j + 2]! = bs[j]!.llo ∧ (sevens bs)[7 * j + 3]! = bs[j]!.lhi ∧
      (sevens bs)[7 * j + 4]! = bs[j]!.hlo ∧ (sevens bs)[7 * j + 5]! = bs[j]!.hhi ∧
      (sevens bs)[7 * j + 6]! = (if bs[j]!.mark == 2 then 1.0 else 0.0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := sevens_get bs h hj (c := 0) (by norm_num); rw [Nat.add_zero] at this; rw [this]; rfl
  · rw [sevens_get bs h hj (c := 1) (by norm_num)]; rfl
  · rw [sevens_get bs h hj (c := 2) (by norm_num)]; rfl
  · rw [sevens_get bs h hj (c := 3) (by norm_num)]; rfl
  · rw [sevens_get bs h hj (c := 4) (by norm_num)]; rfl
  · rw [sevens_get bs h hj (c := 5) (by norm_num)]; rfl
  · rw [sevens_get bs h hj (c := 6) (by norm_num)]; rfl

theorem sevens_size (bs : Array Box) (h : bs.size ≤ 65536) : (sevens bs).size = 7 * bs.size := by
  unfold sevens
  rw [build_size, UInt64.toNat_mul, LeanExe.Dialect.size_toUInt64 bs (by omega)]
  simp only [UInt64.reduceToNat]
  omega

/-- `(φ, λ, h)` lies in box `j` of the output: the box whose ends are at indices `4 + 7j` to
`9 + 7j`, with its label at index `10 + 7j`. -/
def InOut (out : Array Float) (j : Nat) (φ lam h : ℝ) : Prop :=
  10 + 7 * j < out.size ∧ val out[4 + 7 * j]! ≤ φ ∧ φ ≤ val out[5 + 7 * j]! ∧
    val out[6 + 7 * j]! ≤ lam ∧ lam ≤ val out[7 + 7 * j]! ∧ val out[8 + 7 * j]! ≤ h ∧
    h ≤ val out[9 + 7 * j]!

/-- `(φ, λ, h)` lies in a returned box. -/
def Returned (out : Array Float) (φ lam h : ℝ) : Prop := ∃ j, InOut out j φ lam h

/-- The box `j` of the output, with mark 2 for label 1 and mark 1 otherwise. -/
def boxAt (out : Array Float) (j : Nat) : Box :=
  ⟨out[4 + 7 * j]!, out[5 + 7 * j]!, out[6 + 7 * j]!, out[7 + 7 * j]!, out[8 + 7 * j]!,
    out[9 + 7 * j]!, if out[10 + 7 * j]! == 1.0 then 2 else 1⟩

end Demos.Geolocation
