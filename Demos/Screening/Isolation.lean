import Demos.Screening.Filters

/-!
Soundness of the isolation.  `spanTest_zero` states that a cell that the test excludes holds no
time at which the trajectories lie within the threshold `T`, by the speed bound M3, and
`spanTest_certain` that a cell marked certain holds such a time.  `isolate_inv` keeps the
invariant of the levels: at most `2²⁰` cells, each with finite ends, and every close approach of
the window in a cell.  `finalSpans_spec`, `merge_spec`, and `triples_spec` carry the close
approaches and the certainty to the intervals of the output (I1 and I2).
-/

namespace Demos.Screening

open LeanExe.ProofKit LeanExe.Dialect Library.Numerics.Bounds Library.Numerics.Interval
open Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

/-- The time `t` lies in the cell. -/
def Mem1 (s : Span) (t : ℝ) : Prop := val s.lo ≤ t ∧ t ≤ val s.hi

/-- The time `t` lies in the interval. -/
def MemF (f : Found) (t : ℝ) : Prop := val f.lo ≤ t ∧ t ≤ val f.hi

/-- The cell's ends are finite. -/
def FiniteSpan (s : Span) : Prop := Finite s.lo.toBits ∧ Finite s.hi.toBits

section Iso

variable {o1 o2 : Obj} {mu : ℝ} {orb1 orb2 : Orbit} {thr : Interval} {T : ℝ}

/-- The separation of the two trajectories at `t`. -/
noncomputable def sepAt (mu : ℝ) (orb1 orb2 : Orbit) (t : ℝ) : ℝ :=
  dist3 (orb1.position mu t) (orb2.position mu t)

/-- **I1, the exclusion of a cell.**  A cell that the test excludes holds no time at which the
trajectories lie within `T`. -/
theorem spanTest_zero (v1 : orb1.Valid) (v2 : orb2.Valid) (e1 : Encl o1 mu orb1)
    (e2 : Encl o2 mu orb2) (ht : Encloses thr T) {s : Span}
    (h : spanTest Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) s = 0) {t : ℝ}
    (hm : Mem1 s t) : T < sepAt mu orb1 orb2 t := by
  simp only [spanTest] at h
  generalize middle s.lo s.hi = m at h
  split_ifs at h with hA
  all_goals try simp at h
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hA
    obtain ⟨⟨⟨⟨hd, hr⟩, hb⟩, hpos⟩, hlt⟩ := hA
    obtain ⟨fm, -, hreach⟩ := reach_sound hr
    have hdist : |t - val m| ≤ val (reach ⟨0, s.lo, s.hi⟩ m).value := hreach t hm.1 hm.2
    generalize reach ⟨0, s.lo, s.hi⟩ m = r at hr hb hpos hlt hdist
    have cd := gapSq_encl (positionAt_encl e1 m) (positionAt_encl e2 m) hd
    have cbound := encloses_add ht (encloses_mul (encloses_add e1.speed e2.speed)
      (encloses_point r.value))
    have cb2 := encloses_mul cbound cbound hb
    obtain ⟨sb, -, -⟩ := mul_sound hb
    have cB := cbound sb
    generalize hBdef : T + (orb1.speed mu + orb2.speed mu) * val r.value = B at cB cb2
    have hB0 : 0 ≤ B := by
      obtain ⟨z0, zv⟩ := zero_value
      have := (le_iff_value z0 cB.2.1).mp hpos
      rw [zv] at this
      exact this.trans cB.2.2.2.1
    have hm2 := lt_of_sq_lt (dist3_nonneg _ _) (lt_of_hi_lt_lo cb2 cd hlt)
    have l1 := position_lipschitz v1 (mu := mu) t (val m)
    have l2 := position_lipschitz v2 (mu := mu) t (val m)
    have s1 := speed_nonneg (mu := mu) v1
    have s2 := speed_nonneg (mu := mu) v2
    have k1 := mul_le_mul_of_nonneg_left hdist s1
    have k2 := mul_le_mul_of_nonneg_left hdist s2
    have tri1 := dist3_triangle (orb1.position mu (val m)) (orb1.position mu t)
      (orb2.position mu (val m))
    have tri2 := dist3_triangle (orb1.position mu t) (orb2.position mu t)
      (orb2.position mu (val m))
    rw [dist3_comm (orb1.position mu (val m)) (orb1.position mu t)] at tri1
    unfold sepAt
    nlinarith

/-- **I2, the certainty of a cell.**  A cell with finite ends that the test neither excludes nor
merely keeps holds a time at which the trajectories lie within `T`. -/
theorem spanTest_certain (e1 : Encl o1 mu orb1) (e2 : Encl o2 mu orb2) (ht : Encloses thr T)
    (hT : 0 ≤ T) {s : Span} (hf : FiniteSpan s)
    (h0 : spanTest Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) s ≠ 0)
    (h1 : spanTest Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) s ≠ 1) :
    ∃ t, Mem1 s t ∧ sepAt mu orb1 orb2 t ≤ T := by
  simp only [spanTest] at h0 h1
  generalize middle s.lo s.hi = m at h0 h1
  split_ifs at h0 h1 with hA hB
  all_goals try simp at h0
  all_goals try simp at h1
  all_goals
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
    obtain ⟨⟨⟨⟨⟨hd, ht2⟩, hfm⟩, hlo⟩, hhi⟩, hle⟩ := hB
    have fm : Finite m.toBits := (finite_iff m).mp (decide_eq_true hfm)
    have cd := gapSq_encl (positionAt_encl e1 m) (positionAt_encl e2 m) hd
    refine ⟨val m, ⟨(le_iff_value hf.1 fm).mp hlo, (le_iff_value fm hf.2).mp hhi⟩, ?_⟩
    exact le_of_sq_le hT (le_of_hi_le_lo cd (encloses_mul ht ht ht2) hle)

/-! ### The levels -/

/-- The step of `refineSpans` for one cell. -/
def spanStep (o1 o2 : Obj) (thr thr2 : Interval) (s : Span) (acc : Array Span) : Array Span :=
  if spanTest Trig.invPi Trig.halfPi o1 o2 thr thr2 s == 0 then acc
  else
    if (spanTest Trig.invPi Trig.halfPi o1 o2 thr thr2 s != 3 && finite (middle s.lo s.hi) &&
        s.lo < middle s.lo s.hi && middle s.lo s.hi < s.hi) = true then
      (acc.push ⟨s.lo, middle s.lo s.hi⟩).push ⟨middle s.lo s.hi, s.hi⟩
    else acc.push s

theorem refineSpans_eq (thr thr2 : Interval) (cells : Array Span) :
    refineSpans Trig.invPi Trig.halfPi o1 o2 thr thr2 cells =
      LeanExe.loop cells.size.toUInt64 #[] fun i acc =>
        spanStep o1 o2 thr thr2 cells[i.toNat]! acc :=
  rfl

theorem spanStep_extends (thr thr2 : Interval) (s : Span) :
    Extends (spanStep o1 o2 thr thr2 s) := fun acc => by
  unfold spanStep
  split_ifs
  · exact extends_id acc
  · exact extends_push (extends_push extends_id _) _ acc
  · exact extends_push extends_id _ acc

theorem spanStep_size (thr thr2 : Interval) (s : Span) (acc : Array Span) :
    (spanStep o1 o2 thr thr2 s acc).size ≤ acc.size + 2 := by
  unfold spanStep
  split_ifs <;> simp

theorem spanStep_finite (thr thr2 : Interval) {s : Span} (hs : FiniteSpan s) (acc : Array Span)
    (j : Nat) (hj0 : acc.size ≤ j) (hj : j < (spanStep o1 o2 thr thr2 s acc).size) :
    FiniteSpan (spanStep o1 o2 thr thr2 s acc)[j]! := by
  unfold spanStep at hj ⊢
  split_ifs at hj ⊢ with h0 h1
  · omega
  · simp only [Bool.and_eq_true] at h1
    have fm := (finite_iff _).mp h1.1.1.2
    simp only [Array.size_push] at hj
    by_cases hj1 : j = acc.size
    · subst hj1
      rw [push_get_lt _ _ (by simp), push_get_size]
      exact ⟨hs.1, fm⟩
    · have : j = acc.size + 1 := by omega
      subst this
      rw [show acc.size + 1 = (acc.push ⟨s.lo, middle s.lo s.hi⟩).size by simp, push_get_size]
      exact ⟨fm, hs.2⟩
  · simp only [Array.size_push] at hj
    have : j = acc.size := by omega
    subst this
    rw [push_get_size]
    exact hs

theorem spanStep_cover (v1 : orb1.Valid) (v2 : orb2.Valid) (e1 : Encl o1 mu orb1)
    (e2 : Encl o2 mu orb2) (ht : Encloses thr T) {s : Span} {t : ℝ} (hm : Mem1 s t)
    (hc : sepAt mu orb1 orb2 t ≤ T) (acc : Array Span) :
    ∃ j < (spanStep o1 o2 thr (mul thr thr) s acc).size,
      Mem1 (spanStep o1 o2 thr (mul thr thr) s acc)[j]! t := by
  unfold spanStep
  by_cases h0 : spanTest Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) s = 0
  · exact absurd hc (not_le.mpr (spanTest_zero v1 v2 e1 e2 ht h0 hm))
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
structure IsoInv (mu : ℝ) (orb1 orb2 : Orbit) (T t0 t1 : ℝ) (s : Search) : Prop where
  size : s.cells.size ≤ 1048576
  fin : ∀ j < s.cells.size, FiniteSpan s.cells[j]!
  cover : ∀ t, t0 ≤ t → t ≤ t1 → sepAt mu orb1 orb2 t ≤ T →
    ∃ j < s.cells.size, Mem1 s.cells[j]! t
  status : s.status = 0 ∨ s.status = 3

theorem isolateLevel_inv (v1 : orb1.Valid) (v2 : orb2.Valid) (e1 : Encl o1 mu orb1)
    (e2 : Encl o2 mu orb2) (ht : Encloses thr T) {t0 t1 : ℝ} {cap : UInt64}
    (hcap : cap.toNat ≤ 1048576) {s : Search} (h : IsoInv mu orb1 orb2 T t0 t1 s) :
    IsoInv mu orb1 orb2 T t0 t1
      (isolateLevel Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) cap s) := by
  unfold isolateLevel
  by_cases hv : s.status = 0
  · simp only [hv, beq_self_eq_true, ite_true]
    have h64 : s.cells.size < 2 ^ 64 := by have := h.size; omega
    rw [refineSpans_eq]
    set next := (LeanExe.loop s.cells.size.toUInt64 #[] fun i acc =>
      spanStep o1 o2 thr (mul thr thr) s.cells[i.toNat]! acc) with hnext
    have hsize : next.size ≤ 2 * s.cells.size :=
      loop_size_le s.cells h64 _ (fun c acc => spanStep_size _ _ c acc)
    have hn64 : next.size < 2 ^ 64 := by have := h.size; omega
    have parts := fun (t : ℝ) => loop_cover s.cells h64 (spanStep o1 o2 thr (mul thr thr))
      (fun c => spanStep_extends _ _ c) FiniteSpan
      (fun i hi acc j hj0 hj => spanStep_finite _ _ (h.fin i hi) acc j hj0 hj)
      (fun c => Mem1 c t ∧ sepAt mu orb1 orb2 t ≤ T) (fun c => Mem1 c t)
      (fun _ _ hin acc => spanStep_cover v1 v2 e1 e2 ht hin.1 hin.2 acc)
    by_cases hle : next.size.toUInt64 ≤ cap
    · simp only [hle, ite_true]
      have : next.size ≤ 1048576 := by
        have h1 := size_toUInt64 next hn64
        have h2 : next.size.toUInt64.toNat ≤ cap.toNat := hle
        omega
      refine ⟨this, (parts 0).1, fun t a b c => ?_, Or.inl rfl⟩
      obtain ⟨i, hi, hm⟩ := h.cover t a b c
      exact (parts t).2 ⟨i, hi, hm, c⟩
    · simp only [hle, ite_false]
      exact ⟨h.size, h.fin, h.cover, Or.inr rfl⟩
  · simp only [beq_iff_eq, hv, ite_false]
    exact h

theorem isolate_inv (v1 : orb1.Valid) (v2 : orb2.Valid) (e1 : Encl o1 mu orb1)
    (e2 : Encl o2 mu orb2) (ht : Encloses thr T) {t0 t1 : Float} (f0 : Finite t0.toBits)
    (f1 : Finite t1.toBits) {levels cap : UInt64} (hcap : cap.toNat ≤ 1048576) :
    IsoInv mu orb1 orb2 T (val t0) (val t1)
      (isolate Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) t0 t1 levels cap) := by
  refine loop_induction (n := levels) (P := fun _ s => IsoInv mu orb1 orb2 T (val t0) (val t1) s)
    ⟨by simp, fun j hj => ?_, fun t a b _ => ⟨0, by simp, ?_⟩, Or.inl rfl⟩
    (fun _ s _ hs => isolateLevel_inv v1 v2 e1 e2 ht hcap hs)
  · have : j = 0 := by simpa using hj
    subst this
    show FiniteSpan ((#[] : Array Span).push ⟨t0, t1⟩)[(#[] : Array Span).size]!
    rw [push_get_size]
    exact ⟨f0, f1⟩
  · show Mem1 ((#[] : Array Span).push ⟨t0, t1⟩)[(#[] : Array Span).size]! t
    rw [push_get_size]
    exact ⟨a, b⟩

/-! ### The final pass -/

/-- An interval with finite ends, certainty 0 or 1, and a close approach when certain. -/
structure KeepF (mu : ℝ) (orb1 orb2 : Orbit) (T : ℝ) (f : Found) : Prop where
  lo : Finite f.lo.toBits
  hi : Finite f.hi.toBits
  flag : f.certain = 0 ∨ f.certain = 1
  certain : f.certain = 1 → ∃ t, MemF f t ∧ sepAt mu orb1 orb2 t ≤ T

/-- The step of `finalSpans` for one cell. -/
def finalStep (o1 o2 : Obj) (thr thr2 : Interval) (s : Span) (acc : Array Found) : Array Found :=
  if spanTest Trig.invPi Trig.halfPi o1 o2 thr thr2 s == 0 then acc
  else acc.push ⟨s.lo, s.hi,
    if spanTest Trig.invPi Trig.halfPi o1 o2 thr thr2 s == 1 then 0 else 1⟩

theorem finalSpans_eq (thr thr2 : Interval) (cells : Array Span) :
    finalSpans Trig.invPi Trig.halfPi o1 o2 thr thr2 cells =
      LeanExe.loop cells.size.toUInt64 #[] fun i acc =>
        finalStep o1 o2 thr thr2 cells[i.toNat]! acc :=
  rfl

theorem finalSpans_spec (v1 : orb1.Valid) (v2 : orb2.Valid) (e1 : Encl o1 mu orb1)
    (e2 : Encl o2 mu orb2) (ht : Encloses thr T) (hT : 0 ≤ T) {cells : Array Span}
    (hsize : cells.size ≤ 1048576) (hfin : ∀ j < cells.size, FiniteSpan cells[j]!) :
    let r := finalSpans Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) cells
    r.size ≤ cells.size ∧ (∀ j < r.size, KeepF mu orb1 orb2 T r[j]!) ∧
      ∀ t, (∃ i < cells.size, Mem1 cells[i]! t) → sepAt mu orb1 orb2 t ≤ T →
        ∃ j < r.size, MemF r[j]! t := by
  intro r
  have h64 : cells.size < 2 ^ 64 := by omega
  have hext : ∀ c, Extends (finalStep o1 o2 thr (mul thr thr) c) := fun c acc => by
    unfold finalStep
    split_ifs <;> first | exact extends_id acc | exact extends_push extends_id _ acc
  have hsz : r.size ≤ 1 * cells.size := by
    rw [show r = _ from finalSpans_eq _ _ cells]
    exact loop_size_le cells h64 _ (fun c acc => by unfold finalStep; split_ifs <;> simp)
  have parts := fun (t : ℝ) => loop_cover cells h64 (finalStep o1 o2 thr (mul thr thr)) hext
    (KeepF mu orb1 orb2 T)
    (fun i hi acc j hj0 hj => by
      unfold finalStep at hj ⊢
      by_cases h0 : spanTest Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) cells[i]! = 0
      · simp only [h0, beq_self_eq_true, ite_true] at hj; omega
      · simp only [beq_iff_eq, h0, ite_false, Array.size_push] at hj ⊢
        have : j = acc.size := by omega
        subst this
        rw [push_get_size]
        refine ⟨(hfin i hi).1, (hfin i hi).2, ?_, fun hc => ?_⟩
        · dsimp only
          split_ifs <;> simp
        · dsimp only at hc
          split_ifs at hc with h2
          · simp at hc
          · exact spanTest_certain e1 e2 ht hT (hfin i hi) h0 h2)
    (fun c => Mem1 c t ∧ sepAt mu orb1 orb2 t ≤ T) (fun f => MemF f t)
    (fun i _ hin acc => by
      unfold finalStep
      by_cases h0 : spanTest Trig.invPi Trig.halfPi o1 o2 thr (mul thr thr) cells[i]! = 0
      · exact absurd hin.2 (not_le.mpr (spanTest_zero v1 v2 e1 e2 ht h0 hin.1))
      · simp only [beq_iff_eq, h0, ite_false]
        exact ⟨acc.size, by simp, by rw [push_get_size]; exact hin.1⟩)
  refine ⟨by omega, (parts 0).1, fun t ⟨i, hi, hm⟩ hc => (parts t).2 ⟨i, hi, hm, hc⟩⟩

/-! ### The merge -/

theorem mergeStep_hull {a b : Found} (ha : Finite a.lo.toBits ∧ Finite a.hi.toBits)
    (hb : Finite b.lo.toBits ∧ Finite b.hi.toBits) :
    Finite (fmin a.lo b.lo).toBits ∧ Finite (fmax a.hi b.hi).toBits ∧
      (∀ t, MemF a t → MemF ⟨fmin a.lo b.lo, fmax a.hi b.hi, 0⟩ t) ∧
      (∀ t, MemF b t → MemF ⟨fmin a.lo b.lo, fmax a.hi b.hi, 0⟩ t) := by
  obtain ⟨fl, vl⟩ := fmin_value ha.1 hb.1
  obtain ⟨fh, vh⟩ := fmax_value ha.2 hb.2
  refine ⟨fl, fh, fun t ⟨h1, h2⟩ => ?_, fun t ⟨h1, h2⟩ => ?_⟩ <;>
    exact ⟨by show val (fmin a.lo b.lo) ≤ t; unfold val; rw [vl]; simp [h1],
      by show t ≤ val (fmax a.hi b.hi); unfold val; rw [vh]; simp [h2]⟩

/-- The invariant of the merge after `k` cells, for a close approach at `t`. -/
structure MergeInv (mu : ℝ) (orb1 orb2 : Orbit) (T : ℝ) (xs : Array Found) (t : ℝ) (k : Nat)
    (m : Merge) : Prop where
  out : ∀ j < m.out.size, KeepF mu orb1 orb2 T m.out[j]!
  cur : m.has = true → KeepF mu orb1 orb2 T m.cur
  size : m.out.size + (if m.has then 1 else 0) ≤ k
  cover : ∀ i < k, MemF xs[i]! t → (∃ j < m.out.size, MemF m.out[j]! t) ∨
    (m.has = true ∧ MemF m.cur t)

theorem mergeStep_inv {xs : Array Found} {t : ℝ} {k : Nat} (hk : k < xs.size)
    (hx : KeepF mu orb1 orb2 T xs[k]!) {m : Merge} (h : MergeInv mu orb1 orb2 T xs t k m) :
    MergeInv mu orb1 orb2 T xs t (k + 1) (mergeStep m xs[k]!) := by
  unfold mergeStep
  by_cases hh : m.has = true
  · have hc := h.cur hh
    simp only [hh, ite_true]
    by_cases ho : xs[k]!.lo ≤ m.cur.hi
    · simp only [ho, ite_true]
      obtain ⟨fl, fh, ha, hb⟩ := mergeStep_hull ⟨hc.lo, hc.hi⟩ ⟨hx.lo, hx.hi⟩
      refine ⟨h.out, fun _ => ⟨fl, fh, by split_ifs <;> simp [hc.flag], fun hcert => ?_⟩,
        by have := h.size; simp only [hh, ite_true] at this ⊢; omega, fun i hi hm => ?_⟩
      · split_ifs at hcert with h1
        · obtain ⟨u, hu, hs⟩ := hx.certain (beq_iff_eq.mp h1)
          exact ⟨u, hb u hu, hs⟩
        · obtain ⟨u, hu, hs⟩ := hc.certain hcert
          exact ⟨u, ha u hu, hs⟩
      · by_cases hik : i < k
        · rcases h.cover i hik hm with hl | ⟨-, hr⟩
          · exact Or.inl hl
          · exact Or.inr ⟨rfl, ha t hr⟩
        · have : i = k := by omega
          subst this
          exact Or.inr ⟨rfl, hb t hm⟩
    · simp only [ho, ite_false]
      refine ⟨fun j hj => ?_, fun _ => hx, ?_, fun i hi hm => ?_⟩
      · simp only [Array.size_push] at hj
        by_cases hj1 : j < m.out.size
        · rw [push_get_lt _ _ hj1]; exact h.out j hj1
        · have : j = m.out.size := by omega
          subst this
          rw [push_get_size]; exact hc
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

theorem merge_spec {xs : Array Found} (hxs : xs.size ≤ 1048576)
    (hk : ∀ j < xs.size, KeepF mu orb1 orb2 T xs[j]!) :
    (merge xs).size ≤ xs.size ∧ (∀ j < (merge xs).size, KeepF mu orb1 orb2 T (merge xs)[j]!) ∧
      ∀ t, (∃ i < xs.size, MemF xs[i]! t) → ∃ j < (merge xs).size, MemF (merge xs)[j]! t := by
  have h64 : xs.size < 2 ^ 64 := by omega
  have hn := size_toUInt64 xs h64
  have inv := fun (t : ℝ) => loop_induction (n := xs.size.toUInt64)
    (init := (⟨#[], ⟨0.0, 0.0, 0⟩, false⟩ : Merge)) (f := fun i m => mergeStep m xs[i.toNat]!)
    (fun k m => k ≤ xs.size → MergeInv mu orb1 orb2 T xs t k m)
    (fun _ => ⟨fun j hj => absurd hj (by simp), fun h => absurd h (by decide), by simp,
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩)
    (fun k m hk' ih _ => by
      rw [hn] at hk'
      have hk'' : (UInt64.ofNat k).toNat = k := by rw [UInt64.toNat_ofNat']; omega
      simp only [hk'']
      exact mergeStep_inv hk' (hk k hk') (ih (by omega)))
  simp only [hn] at inv
  unfold merge
  dsimp only
  generalize LeanExe.loop xs.size.toUInt64 (⟨#[], ⟨0.0, 0.0, 0⟩, false⟩ : Merge)
    (fun i m => mergeStep m xs[i.toNat]!) = m at inv ⊢
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

theorem uint_div_mod (m : Nat) (hm : m < 2 ^ 64) :
    ((UInt64.ofNat m) / 3).toNat = m / 3 ∧ ((UInt64.ofNat m) % 3).toNat = m % 3 := by
  have h : (UInt64.ofNat m).toNat = m := by rw [UInt64.toNat_ofNat']; omega
  exact ⟨by rw [UInt64.toNat_div, h]; rfl, by rw [UInt64.toNat_mod, h]; rfl⟩

theorem triples_spec (ys : Array Found) (h : ys.size ≤ 1048576) :
    (triples ys).size = 3 * ys.size ∧ ∀ j < ys.size,
      (triples ys)[3 * j]! = ys[j]!.lo ∧ (triples ys)[3 * j + 1]! = ys[j]!.hi ∧
        (triples ys)[3 * j + 2]! = ys[j]!.certain.toFloat := by
  have hn : (3 * ys.size.toUInt64).toNat = 3 * ys.size := by
    rw [UInt64.toNat_mul, size_toUInt64 ys (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  have at3 : ∀ q, q < 3 * ys.size →
      (triples ys)[q]! = (let y := ys[(UInt64.ofNat q / 3).toNat]!
        if UInt64.ofNat q % 3 == 0 then y.lo else if UInt64.ofNat q % 3 == 1 then y.hi
        else y.certain.toFloat) := fun q hq => by
    unfold triples
    rw [build_get (by rw [hn]; exact hq)]
  refine ⟨by unfold triples; rw [build_size, hn], fun j hj => ⟨?_, ?_, ?_⟩⟩
  · rw [at3 (3 * j) (by omega)]
    obtain ⟨d, m⟩ := uint_div_mod (3 * j) (by omega)
    have hd : (UInt64.ofNat (3 * j) / 3).toNat = j := by rw [d]; omega
    have hm : UInt64.ofNat (3 * j) % 3 = 0 := UInt64.toNat_inj.mp (by rw [m]; simp)
    simp only [hd, hm, beq_self_eq_true, ite_true]
  · rw [at3 (3 * j + 1) (by omega)]
    obtain ⟨d, m⟩ := uint_div_mod (3 * j + 1) (by omega)
    have hd : (UInt64.ofNat (3 * j + 1) / 3).toNat = j := by rw [d]; omega
    have hm : UInt64.ofNat (3 * j + 1) % 3 = 1 := UInt64.toNat_inj.mp (by rw [m]; simp)
    simp only [hd, hm]
    rfl
  · rw [at3 (3 * j + 2) (by omega)]
    obtain ⟨d, m⟩ := uint_div_mod (3 * j + 2) (by omega)
    have hd : (UInt64.ofNat (3 * j + 2) / 3).toNat = j := by rw [d]; omega
    have hm : UInt64.ofNat (3 * j + 2) % 3 = 2 := UInt64.toNat_inj.mp (by rw [m]; simp)
    simp only [hd, hm]
    rfl

end Iso

end Demos.Screening
