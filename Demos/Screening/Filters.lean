import Demos.Screening.Program
import Demos.Screening.Cover
import Library.Numerics.Interval.Proof

/-!
The enclosures of an object's quantities and positions, and the soundness of the two filters.
`apsidesExclude_sound` states that a pair that the apogee–perigee filter excludes has every point
of one path farther than the threshold from every point of the other (F1).  `pathFilter_inv`
states the invariant of the orbit-path filter: every pair of eccentric anomalies in `[0, 2π]`
whose path points lie within the threshold lies in a cell of the search, and `pathFilter_sound`
derives from it that verdict 1 excludes the pair, and `pathFilter_close` that verdict 2 finds two
path points within the threshold (F2).
-/

namespace Demos.Screening

open LeanExe.ProofKit LeanExe.Dialect Library.Numerics.Bounds Library.Numerics.Interval
open Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

/-- The real value of a float. -/
noncomputable abbrev val (x : Float) : ℝ := value x.toBits

theorem encloses_point (x : Float) : Encloses (point x) (val x) := fun h => (point_sound h).2

theorem encloses_make {lo hi : Float} {x : ℝ} (h1 : val lo ≤ x) (h2 : x ≤ val hi) :
    Encloses (make lo hi) x := fun h => (make_sound h).2.2.2 x h1 h2

theorem lt_of_hi_lt_lo {a b : Interval} {x y : ℝ} (ha : Contains a x) (hb : Contains b y)
    (h : a.hi < b.lo) : x < y := by
  have := (lt_iff_value ha.2.2.1 hb.2.1).mp h
  linarith [ha.2.2.2.2, hb.2.2.2.1]

theorem le_of_hi_le_lo {a b : Interval} {x y : ℝ} (ha : Contains a x) (hb : Contains b y)
    (h : a.hi ≤ b.lo) : x ≤ y := by
  have := (le_iff_value ha.2.2.1 hb.2.1).mp h
  linarith [ha.2.2.2.2, hb.2.2.2.1]

/-! ### Objects and positions -/

/-- The intervals of an object contain the quantities of an orbit for the gravitational
parameter `mu`. -/
structure Encl (o : Obj) (mu : ℝ) (orb : Orbit) : Prop where
  a : Encloses o.a orb.a
  e : Encloses o.e orb.e
  beta : Encloses o.beta orb.beta
  px : Encloses o.px orb.toPerigee.1
  py : Encloses o.py orb.toPerigee.2.1
  pz : Encloses o.pz orb.toPerigee.2.2
  qx : Encloses o.qx orb.ahead.1
  qy : Encloses o.qy orb.ahead.2.1
  qz : Encloses o.qz orb.ahead.2.2
  n : Encloses o.n (orb.motion mu)
  m0 : Encloses o.m0 orb.m0
  epoch : Encloses o.epoch orb.epoch
  speed : Encloses o.speed (orb.speed mu)
  perigee : Encloses o.perigee (orb.a * (1 - orb.e))
  apogee : Encloses o.apogee (orb.a * (1 + orb.e))

/-- The orbit of the real values of seven floats. -/
noncomputable def orbitOf (a e incl node argp m0 epoch : Float) : Orbit :=
  ⟨val a, val e, val incl, val node, val argp, val m0, val epoch⟩

theorem object_encl (mu a e incl node argp m0 epoch : Float) :
    Encl (object Trig.invPi Trig.halfPi mu a e incl node argp m0 epoch) (val mu)
      (orbitOf a e incl node argp m0 epoch) := by
  have h := Spec.orbit.encloses (powLog := Trig.invPi) (powExp := Trig.invPi)
    (encloses_point mu) (encloses_point a) (encloses_point e) (encloses_point incl)
    (encloses_point node) (encloses_point argp)
  rw [show Spec.orbit (val mu) (val a) (val e) (val incl) (val node) (val argp) =
    Spec.orbit (val mu) (orbitOf a e incl node argp m0 epoch).a
      (orbitOf a e incl node argp m0 epoch).e (orbitOf a e incl node argp m0 epoch).incl
      (orbitOf a e incl node argp m0 epoch).node (orbitOf a e incl node argp m0 epoch).argp
    from rfl, Spec.orbit_eq (val mu) (orbitOf a e incl node argp m0 epoch)] at h
  unfold object
  generalize Spec.orbitI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point mu) (point a)
    (point e) (point incl) (point node) (point argp) = c at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨encloses_point a, encloses_point e, h2, h3, h4, h5, h6, h7, h8, h1, encloses_point m0,
    encloses_point epoch, h9, h10, h11⟩

/-- Three intervals contain the coordinates of a point. -/
def Encl3 (p : Interval × Interval × Interval) (q : ℝ × ℝ × ℝ) : Prop :=
  Encloses p.1 q.1 ∧ Encloses p.2.1 q.2.1 ∧ Encloses p.2.2 q.2.2

theorem pointAt_encl {o : Obj} {mu : ℝ} {orb : Orbit} (h : Encl o mu orb) {E : Interval} {x : ℝ}
    (hE : Encloses E x) : Encl3 (pointAt Trig.invPi Trig.halfPi o E) (orb.path x) :=
  Spec.pathPoint.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) h.a h.e h.beta h.px h.py
    h.pz h.qx h.qy h.qz hE

theorem positionAt_encl {o : Obj} {mu : ℝ} {orb : Orbit} (h : Encl o mu orb) (t : Float) :
    Encl3 (positionAt Trig.invPi Trig.halfPi o t) (orb.position mu (val t)) :=
  pointAt_encl h (Spec.anomaly.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) h.e h.n
    h.m0 h.epoch (encloses_point t))

theorem gapSq_encl {p q : Interval × Interval × Interval} {P Q : ℝ × ℝ × ℝ} (hp : Encl3 p P)
    (hq : Encl3 q Q) : Encloses (gapSq Trig.invPi Trig.halfPi p q) (dist3 P Q ^ 2) := by
  have := Spec.distSq.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) hp.1 hp.2.1 hp.2.2
    hq.1 hq.2.1 hq.2.2
  rwa [Spec.distSq_eq] at this

/-- A squared distance above the square of a threshold puts the distance above the threshold. -/
theorem lt_of_sq_lt {T d : ℝ} (hd : 0 ≤ d) (h : T * T < d ^ 2) : T < d := by
  nlinarith

theorem le_of_sq_le {T d : ℝ} (hT : 0 ≤ T) (h : d ^ 2 ≤ T * T) : d ≤ T := by
  nlinarith

/-! ### F1: the apogee–perigee filter -/

/-- The points of two paths lie at least the gap between the second's perigee radius and the
first's apogee radius apart. -/
theorem apsides_gap {o1 o2 : Orbit} (h1 : o1.Valid) (h2 : o2.Valid) {T : ℝ}
    (hg : T < o2.a * (1 - o2.e) - o1.a * (1 + o1.e)) (E1 E2 : ℝ) :
    T < dist3 (o1.path E1) (o2.path E2) := by
  have r1 := (path_radius h1 E1).2
  have r2 := (path_radius h2 E2).1
  have tri := dist3_triangle (o2.path E2) (o1.path E1) (0, 0, 0)
  rw [dist3_comm (o2.path E2) (o1.path E1)] at tri
  linarith

/-- **F1.**  When the apogee–perigee filter excludes the pair, every point of one path lies farther
than the threshold `T` from every point of the other. -/
theorem apsidesExclude_sound {o1 o2 : Obj} {mu : ℝ} {orb1 orb2 : Orbit} (e1 : Encl o1 mu orb1)
    (e2 : Encl o2 mu orb2) (v1 : orb1.Valid) (v2 : orb2.Valid) {thr : Interval} {T : ℝ}
    (ht : Encloses thr T) (h : apsidesExclude o1 o2 thr = true) (E1 E2 : ℝ) :
    T < dist3 (orb1.path E1) (orb2.path E2) := by
  simp only [apsidesExclude, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    at h
  obtain ⟨hs, h⟩ := h
  have cT := ht hs
  rcases h with ⟨g, hg⟩ | ⟨g, hg⟩
  · have c := encloses_sub e2.perigee e1.apogee g
    exact apsides_gap v1 v2 (lt_of_hi_lt_lo cT c hg) E1 E2
  · have c := encloses_sub e1.perigee e2.apogee g
    rw [dist3_comm]
    exact apsides_gap v2 v1 (lt_of_hi_lt_lo cT c hg) E2 E1

/-! ### F2: the orbit-path filter -/

/-- The eccentric anomalies `x` and `y` lie in the cell. -/
def Mem2 (c : Cell) (x y : ℝ) : Prop :=
  val c.lo1 ≤ x ∧ x ≤ val c.hi1 ∧ val c.lo2 ≤ y ∧ y ≤ val c.hi2

section Path

variable {o1 o2 : Obj} {mu : ℝ} {orb1 orb2 : Orbit} {thr : Interval} {T : ℝ}

theorem cellExclude_sound (e1 : Encl o1 mu orb1) (e2 : Encl o2 mu orb2)
    (ht : Encloses thr T) {c : Cell}
    (h : cellExclude Trig.invPi Trig.halfPi o1 o2 (mul thr thr) c = true)
    {x y : ℝ} (hm : Mem2 c x y) : T < dist3 (orb1.path x) (orb2.path y) := by
  simp only [cellExclude, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hs, ht2⟩, hlt⟩ := h
  have g := gapSq_encl (pointAt_encl e1 (encloses_make hm.1 hm.2.1))
    (pointAt_encl e2 (encloses_make hm.2.2.1 hm.2.2.2))
  exact lt_of_sq_lt (dist3_nonneg _ _) (lt_of_hi_lt_lo (encloses_mul ht ht ht2) (g hs) hlt)

theorem cellClose_sound (e1 : Encl o1 mu orb1) (e2 : Encl o2 mu orb2)
    (ht : Encloses thr T) (hT : 0 ≤ T) {c : Cell}
    (h : cellClose Trig.invPi Trig.halfPi o1 o2 (mul thr thr) c = true) :
    ∃ x y, dist3 (orb1.path x) (orb2.path y) ≤ T := by
  simp only [cellClose, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hs, ht2⟩, hle⟩ := h
  have g := gapSq_encl (pointAt_encl e1 (encloses_point (middle c.lo1 c.hi1)))
    (pointAt_encl e2 (encloses_point (middle c.lo2 c.hi2)))
  exact ⟨_, _, le_of_sq_le hT
    (le_of_hi_le_lo (g hs) (encloses_mul ht ht ht2) hle)⟩

theorem anyClose_sound (e1 : Encl o1 mu orb1) (e2 : Encl o2 mu orb2)
    (ht : Encloses thr T) (hT : 0 ≤ T) {cells : Array Cell}
    (h : anyClose Trig.invPi Trig.halfPi o1 o2 (mul thr thr) cells = true) :
    ∃ x y, dist3 (orb1.path x) (orb2.path y) ≤ T := by
  have key := loop_induction (n := cells.size.toUInt64) (init := false)
    (f := fun i found =>
      if found then true else cellClose Trig.invPi Trig.halfPi o1 o2 (mul thr thr) cells[i.toNat]!)
    (fun _ found => found = true → ∃ x y, dist3 (orb1.path x) (orb2.path y) ≤ T)
    (fun h => absurd h (by decide))
    (fun k found _ ih hf => by
      by_cases h0 : found = true
      · exact ih h0
      · simp only [h0, Bool.false_eq_true, ite_false] at hf
        exact cellClose_sound e1 e2 ht hT hf)
  exact key h

/-- The step of `refineCells` for one cell. -/
def cellStep (o1 o2 : Obj) (thr2 : Interval) (c : Cell) (acc : Array Cell) : Array Cell :=
  if cellExclude Trig.invPi Trig.halfPi o1 o2 thr2 c then acc
  else
    if finite (middle c.lo1 c.hi1) && finite (middle c.lo2 c.hi2) then
      (((acc.push ⟨c.lo1, middle c.lo1 c.hi1, c.lo2, middle c.lo2 c.hi2⟩).push
        ⟨c.lo1, middle c.lo1 c.hi1, middle c.lo2 c.hi2, c.hi2⟩).push
          ⟨middle c.lo1 c.hi1, c.hi1, c.lo2, middle c.lo2 c.hi2⟩).push
            ⟨middle c.lo1 c.hi1, c.hi1, middle c.lo2 c.hi2, c.hi2⟩
    else acc.push c

theorem refineCells_eq (thr2 : Interval) (cells : Array Cell) :
    refineCells Trig.invPi Trig.halfPi o1 o2 thr2 cells =
      LeanExe.loop cells.size.toUInt64 #[] fun i acc => cellStep o1 o2 thr2 cells[i.toNat]! acc :=
  rfl

theorem cellStep_extends (thr2 : Interval) (c : Cell) : Extends (cellStep o1 o2 thr2 c) :=
  fun acc => by
    unfold cellStep
    split_ifs
    · exact extends_id acc
    · exact extends_push (extends_push (extends_push (extends_push extends_id _) _) _) _ acc
    · exact extends_push extends_id _ acc

theorem cellStep_size (thr2 : Interval) (c : Cell) (acc : Array Cell) :
    (cellStep o1 o2 thr2 c acc).size ≤ acc.size + 4 := by
  unfold cellStep
  split_ifs <;> simp

/-- A cell that holds a close pair leaves a cell of the step that holds it. -/
theorem cellStep_cover (e1 : Encl o1 mu orb1) (e2 : Encl o2 mu orb2) (ht : Encloses thr T)
    {c : Cell} {x y : ℝ} (hm : Mem2 c x y) (hc : dist3 (orb1.path x) (orb2.path y) ≤ T)
    (acc : Array Cell) :
    ∃ j < (cellStep o1 o2 (mul thr thr) c acc).size,
      Mem2 (cellStep o1 o2 (mul thr thr) c acc)[j]! x y := by
  unfold cellStep
  by_cases h1 : cellExclude Trig.invPi Trig.halfPi o1 o2 (mul thr thr) c = true
  · exact absurd hc (not_le.mpr (cellExclude_sound e1 e2 ht h1 hm))
  · simp only [h1, Bool.false_eq_true, ite_false]
    split_ifs with h2
    · set m1 := middle c.lo1 c.hi1
      set m2 := middle c.lo2 c.hi2
      obtain ⟨l1, u1, l2, u2⟩ := hm
      rcases le_total x (val m1) with hx | hx <;> rcases le_total y (val m2) with hy | hy
      · exact ⟨acc.size, by simp only [Array.size_push]; omega, by
          rw [push_get_lt _ _ (by simp only [Array.size_push]; omega),
            push_get_lt _ _ (by simp only [Array.size_push]; omega),
            push_get_lt _ _ (by simp only [Array.size_push]; omega), push_get_size]
          exact ⟨l1, hx, l2, hy⟩⟩
      · exact ⟨acc.size + 1, by simp only [Array.size_push]; omega, by
          rw [push_get_lt _ _ (by simp only [Array.size_push]; omega),
            push_get_lt _ _ (by simp only [Array.size_push]; omega)]
          rw [show acc.size + 1 = (acc.push ⟨c.lo1, m1, c.lo2, m2⟩).size by simp, push_get_size]
          exact ⟨l1, hx, hy, u2⟩⟩
      · exact ⟨acc.size + 2, by simp only [Array.size_push]; omega, by
          rw [push_get_lt _ _ (by simp only [Array.size_push]; omega)]
          rw [show acc.size + 2 = ((acc.push ⟨c.lo1, m1, c.lo2, m2⟩).push
            ⟨c.lo1, m1, m2, c.hi2⟩).size by simp, push_get_size]
          exact ⟨hx, u1, l2, hy⟩⟩
      · exact ⟨acc.size + 3, by simp only [Array.size_push]; omega, by
          rw [show acc.size + 3 = (((acc.push ⟨c.lo1, m1, c.lo2, m2⟩).push
            ⟨c.lo1, m1, m2, c.hi2⟩).push ⟨m1, c.hi1, c.lo2, m2⟩).size by simp, push_get_size]
          exact ⟨hx, u1, hy, u2⟩⟩
    · exact ⟨acc.size, by simp only [Array.size_push]; omega, by rw [push_get_size]; exact hm⟩

/-- The invariant of the orbit-path filter: at most `2²⁰` cells, verdict 1 only with no cell,
verdict 2 only with two path points within `T`, and every pair of eccentric anomalies in
`[0, 2π]` whose path points lie within `T` in a cell. -/
structure PathInv (orb1 orb2 : Orbit) (T : ℝ) (s : PathSearch) : Prop where
  range : s.verdict = 0 ∨ s.verdict = 1 ∨ s.verdict = 2 ∨ s.verdict = 3 ∨ s.verdict = 4
  size : s.cells.size ≤ 1048576
  empty : s.verdict = 1 → s.cells.size = 0
  close : s.verdict = 2 → ∃ x y, dist3 (orb1.path x) (orb2.path y) ≤ T
  cover : ∀ x y, 0 ≤ x → x ≤ 2 * Real.pi → 0 ≤ y → y ≤ 2 * Real.pi →
    dist3 (orb1.path x) (orb2.path y) ≤ T → ∃ j < s.cells.size, Mem2 s.cells[j]! x y

theorem val_zero : val 0.0 = 0 := by
  have hs : Wasm.IEEE64.scaledValue 0 = 0 := by decide +kernel
  have hb : (0.0 : Float).toBits = 0 := by decide +kernel
  simp only [val, hb, value, hs]; norm_num

set_option exponentiation.threshold 2048 in
theorem val_six_half : val 6.5 = 6.5 := by
  have hb : (6.5 : Float).toBits = 0x401A000000000000 := by decide +kernel
  have hs : Wasm.IEEE64.scaledValue 0x401A000000000000 = 13 * 2 ^ 1073 := by decide +kernel
  simp only [val, hb, value, hs]
  push_cast
  rw [pow_succ]
  field_simp
  norm_num

theorem pathInv_init : PathInv orb1 orb2 T
    ⟨(#[] : Array Cell).push ⟨0.0, 6.5, 0.0, 6.5⟩, 0, 0⟩ := by
  have hpi : 2 * Real.pi ≤ 6.5 := by linarith [Real.pi_lt_d2]
  refine ⟨Or.inl rfl, by simp, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun x y hx0 hx1 hy0 hy1 _ => ⟨0, by simp, ?_⟩⟩
  show Mem2 ((#[] : Array Cell).push ⟨0.0, 6.5, 0.0, 6.5⟩)[(#[] : Array Cell).size]! x y
  rw [push_get_size]
  show val 0.0 ≤ x ∧ x ≤ val 6.5 ∧ val 0.0 ≤ y ∧ y ≤ val 6.5
  rw [val_zero, val_six_half]
  exact ⟨hx0, by linarith, hy0, by linarith⟩

theorem pathLevel_inv (e1 : Encl o1 mu orb1) (e2 : Encl o2 mu orb2) (ht : Encloses thr T)
    (hT : 0 ≤ T) {cap : UInt64} (hcap : cap.toNat ≤ 1048576) {s : PathSearch}
    (h : PathInv orb1 orb2 T s) :
    PathInv orb1 orb2 T (pathLevel Trig.invPi Trig.halfPi o1 o2 (mul thr thr) cap s) := by
  unfold pathLevel
  by_cases hv : s.verdict = 0
  · simp only [hv, beq_self_eq_true, ite_true]
    by_cases hc : anyClose Trig.invPi Trig.halfPi o1 o2 (mul thr thr) s.cells = true
    · simp only [hc, ite_true]
      exact ⟨by simp, h.size, fun h => by simp at h, fun _ => anyClose_sound e1 e2 ht hT hc,
        h.cover⟩
    · simp only [hc, Bool.false_eq_true, ite_false]
      have h64 : s.cells.size < 2 ^ 64 := by have := h.size; omega
      rw [refineCells_eq]
      set next := (LeanExe.loop s.cells.size.toUInt64 #[] fun i acc =>
        cellStep o1 o2 (mul thr thr) s.cells[i.toNat]! acc) with hnext
      have hsize : next.size ≤ 4 * s.cells.size :=
        loop_size_le s.cells h64 _ (fun c acc => cellStep_size _ c acc)
      have hn64 : next.size < 2 ^ 64 := by have := h.size; omega
      have ncover : ∀ x y, 0 ≤ x → x ≤ 2 * Real.pi → 0 ≤ y → y ≤ 2 * Real.pi →
          dist3 (orb1.path x) (orb2.path y) ≤ T → ∃ j < next.size, Mem2 next[j]! x y :=
        fun x y a b c d hxy => by
          obtain ⟨i, hi, hm⟩ := h.cover x y a b c d hxy
          exact (loop_cover s.cells h64 (cellStep o1 o2 (mul thr thr))
            (fun c => cellStep_extends _ c) (fun _ => True) (fun _ _ _ _ _ _ => trivial)
            (fun c => Mem2 c x y ∧ dist3 (orb1.path x) (orb2.path y) ≤ T) (fun c => Mem2 c x y)
            (fun _ _ hin acc => cellStep_cover e1 e2 ht hin.1 hin.2 acc)).2 ⟨i, hi, hm, hxy⟩
      by_cases h0 : next.size.toUInt64 = 0
      · have hz : next.size = 0 := by
          have := size_toUInt64 next hn64
          rw [h0] at this
          simpa using this.symm
        simp only [h0, beq_self_eq_true, ite_true]
        refine ⟨by simp, ?_, fun _ => hz, fun h => by simp at h, ncover⟩
        show next.size ≤ 1048576
        omega
      · simp only [beq_iff_eq, h0, ite_false]
        by_cases hle : next.size.toUInt64 ≤ cap
        · simp only [hle, ite_true]
          have : next.size ≤ 1048576 := by
            have h1 := size_toUInt64 next hn64
            have h2 : next.size.toUInt64.toNat ≤ cap.toNat := hle
            omega
          exact ⟨by simp, this, fun h => by simp at h, fun h => by simp at h, ncover⟩
        · simp only [hle, ite_false]
          exact ⟨by simp, h.size, fun h => by simp at h, fun h => by simp at h, h.cover⟩
  · simp only [beq_iff_eq, hv, ite_false]
    exact h

theorem pathFilter_inv (e1 : Encl o1 mu orb1) (e2 : Encl o2 mu orb2) (ht : Encloses thr T)
    (hT : 0 ≤ T) {levels cap : UInt64} (hcap : cap.toNat ≤ 1048576) :
    PathInv orb1 orb2 T (pathFilter Trig.invPi Trig.halfPi o1 o2 (mul thr thr) levels cap) := by
  have key := loop_induction (n := levels)
    (init := (⟨(#[] : Array Cell).push ⟨0.0, 6.5, 0.0, 6.5⟩, 0, 0⟩ : PathSearch))
    (f := fun _ s => pathLevel Trig.invPi Trig.halfPi o1 o2 (mul thr thr) cap s)
    (fun _ s => PathInv orb1 orb2 T s) pathInv_init
    (fun _ s _ hs => pathLevel_inv e1 e2 ht hT hcap hs)
  unfold pathFilter
  dsimp only
  generalize LeanExe.loop levels (⟨(#[] : Array Cell).push ⟨0.0, 6.5, 0.0, 6.5⟩, 0, 0⟩ : PathSearch)
    (fun _ s => pathLevel Trig.invPi Trig.halfPi o1 o2 (mul thr thr) cap s) = s at key ⊢
  split_ifs
  · exact key
  · exact ⟨by simp, key.size, fun h => by simp at h, fun h => by simp at h, key.cover⟩
  · exact key

/-- **F2.**  Verdict 1 of the orbit-path filter puts every point of one path farther than `T` from
every point of the other. -/
theorem pathFilter_sound (e1 : Encl o1 mu orb1)
    (e2 : Encl o2 mu orb2) (ht : Encloses thr T) (hT : 0 ≤ T) {levels cap : UInt64}
    (hcap : cap.toNat ≤ 1048576)
    (h : (pathFilter Trig.invPi Trig.halfPi o1 o2 (mul thr thr) levels cap).verdict = 1)
    (E1 E2 : ℝ) : T < dist3 (orb1.path E1) (orb2.path E2) := by
  have inv := pathFilter_inv e1 e2 ht hT (levels := levels) hcap
  have he := inv.empty h
  obtain ⟨x, hx0, hx1, hx⟩ := path_reduce orb1 E1
  obtain ⟨y, hy0, hy1, hy⟩ := path_reduce orb2 E2
  rw [hx, hy]
  by_contra hc
  obtain ⟨j, hj, -⟩ := inv.cover x y hx0 hx1 hy0 hy1 (not_lt.mp hc)
  omega

/-- **F2.**  Verdict 2 of the orbit-path filter finds two path points within `T`. -/
theorem pathFilter_close (e1 : Encl o1 mu orb1) (e2 : Encl o2 mu orb2) (ht : Encloses thr T)
    (hT : 0 ≤ T) {levels cap : UInt64} (hcap : cap.toNat ≤ 1048576)
    (h : (pathFilter Trig.invPi Trig.halfPi o1 o2 (mul thr thr) levels cap).verdict = 2) :
    ∃ x y, dist3 (orb1.path x) (orb2.path y) ≤ T :=
  (pathFilter_inv e1 e2 ht hT (levels := levels) hcap).close h

end Path

end Demos.Screening
