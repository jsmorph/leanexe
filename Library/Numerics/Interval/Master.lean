import Library.Numerics.Interval.Compiled
import Library.Numerics.Interval.Proof
import Library.Numerics.Bounds.Master
import Verified.Master

namespace Library.Numerics.Interval

open LeanExe.ProofKit Library.Numerics.Bounds
open LeanExe.ProofKit.F64Adjacent (nextUp nextDown)
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

/-! ### Lemmas -/

theorem join_status (ok : Bool) (l h : Checked) :
    (join ok l h).status = 0 ↔ ok = true ∧ l.status = 0 ∧ h.status = 0 := by
  refine ⟨fun hs => ?_, fun ⟨h1, h2, h3⟩ => ?_⟩
  · obtain ⟨h1, h2, h3, -⟩ := join_accepted hs
    exact ⟨h1, h2, h3⟩
  · simp [join, h1, h2, h3]

theorem join_eq {ok : Bool} {l h : Checked} (hs : (join ok l h).status = 0) :
    join ok l h = ⟨0, l.value, h.value⟩ :=
  (join_accepted hs).2.2.2

theorem join_fields {ok : Bool} {l h : Checked} (hs : (join ok l h).status = 0) :
    (join ok l h).lo = l.value ∧ (join ok l h).hi = h.value := by
  rw [join_eq hs]
  exact ⟨rfl, rfl⟩

/-- The acceptance and the endpoints of `join` on a checked value one step below `wl` and a
checked value one step above `wh`. -/
theorem join_endpoints {ok : Bool} {l h : Checked} {okl okh : Prop} {wl wh : UInt64}
    (hl : (l.status = 0 ↔ okl ∧ Finite wl ∧ Finite (nextDown wl)) ∧
      (l.status = 0 → l.value.toBits = nextDown wl))
    (hh : (h.status = 0 ↔ okh ∧ Finite wh ∧ Finite (nextUp wh)) ∧
      (h.status = 0 → h.value.toBits = nextUp wh)) :
    ((join ok l h).status = 0 ↔
        ok = true ∧ (okl ∧ Finite wl ∧ Finite (nextDown wl)) ∧ okh ∧ Finite wh ∧
          Finite (nextUp wh)) ∧
      ((join ok l h).status = 0 →
        (join ok l h).lo.toBits = nextDown wl ∧ (join ok l h).hi.toBits = nextUp wh) := by
  refine ⟨by rw [join_status, hl.1, hh.1], fun hs => ?_⟩
  obtain ⟨-, sl, sh⟩ := (join_status ok l h).mp hs
  obtain ⟨el, eh⟩ := join_fields hs
  rw [el, eh]
  exact ⟨hl.2 sl, hh.2 sh⟩

theorem outward2_spec (up : Bool) (w : Float) :
    ((outward2 up w).status = 0 ↔ Finite w.toBits ∧ Finite (F64Outward.neighbor up w.toBits) ∧
        Finite (F64Outward.neighbor up (F64Outward.neighbor up w.toBits))) ∧
      ((outward2 up w).status = 0 →
        (outward2 up w).value.toBits =
          F64Outward.neighbor up (F64Outward.neighbor up w.toBits)) := by
  refine ⟨⟨fun h => ?_, fun ⟨f1, f2, f3⟩ => ?_⟩, fun h => (outward2_bits h).2.2.2⟩
  · obtain ⟨f1, f2, f3, -⟩ := outward2_bits h
    exact ⟨f1, f2, f3⟩
  · have he : (endpoint up w).status = 0 := (endpoint_spec up w).1.mpr ⟨f1, f2⟩
    have ev := ((endpoint_spec up w).2 he).1
    have he2 : (endpoint up (endpoint up w).value).status = 0 :=
      (endpoint_spec up _).1.mpr ⟨by rw [ev]; exact f2, by rw [ev]; exact f3⟩
    have hb : ((endpoint up w).status == 0) = true := beq_iff_eq.mpr he
    unfold outward2
    simp only [hb, ite_true]
    exact he2

theorem outward2_down (w : Float) :
    ((outward2 false w).status = 0 ↔ Finite w.toBits ∧ Finite (nextDown w.toBits) ∧
        Finite (nextDown (nextDown w.toBits))) ∧
      ((outward2 false w).status = 0 →
        (outward2 false w).value.toBits = nextDown (nextDown w.toBits)) :=
  outward2_spec false w

theorem outward2_up (w : Float) :
    ((outward2 true w).status = 0 ↔ Finite w.toBits ∧ Finite (nextUp w.toBits) ∧
        Finite (nextUp (nextUp w.toBits))) ∧
      ((outward2 true w).status = 0 →
        (outward2 true w).value.toBits = nextUp (nextUp w.toBits)) :=
  outward2_spec true w

theorem outward2_meaning {up : Bool} {w : Float} (h : (outward2 up w).status = 0) {t : ℝ}
    (ht : F64SignedRounding.WithinSteps 1 t w.toBits) :
    if up then t ≤ value (outward2 up w).value.toBits
    else value (outward2 up w).value.toBits ≤ t := by
  cases up
  · exact (outward2_lower ht h).2
  · exact (outward2_upper ht h).2

theorem extreme_status (up : Bool) (p q r s : Checked) :
    (extreme up p q r s).status = 0 ↔
      p.status = 0 ∧ q.status = 0 ∧ r.status = 0 ∧ s.status = 0 := by
  refine ⟨extreme_accepted, fun ⟨h1, h2, h3, h4⟩ => ?_⟩
  cases up <;> simp [extreme, h1, h2, h3, h4]

theorem extreme_value {up : Bool} {p q r s : Checked} (h : (extreme up p q r s).status = 0) :
    (extreme up p q r s).value =
      if up then max (max p.value q.value) (max r.value s.value)
      else min (min p.value q.value) (min r.value s.value) := by
  obtain ⟨h1, h2, h3, h4⟩ := extreme_accepted h
  unfold extreme
  simp only [h1, h2, h3, h4, beq_self_eq_true, Bool.and_self, ite_true]
  cases up <;> rfl

theorem extreme_values {up : Bool} {p q r s : Checked} (h : (extreme up p q r s).status = 0)
    (fp : Finite p.value.toBits) (fq : Finite q.value.toBits) (fr : Finite r.value.toBits)
    (fs : Finite s.value.toBits) :
    Finite (extreme up p q r s).value.toBits ∧ value (extreme up p q r s).value.toBits =
      if up then max (max (value p.value.toBits) (value q.value.toBits))
        (max (value r.value.toBits) (value s.value.toBits))
      else min (min (value p.value.toBits) (value q.value.toBits))
        (min (value r.value.toBits) (value s.value.toBits)) := by
  cases up
  · exact extreme_lower h fp fq fr fs
  · exact extreme_upper h fp fq fr fs

/-- The conditions on the four corners of a product, for the lower and the upper endpoint,
gathered by endpoint and by corner. -/
theorem corners_iff {α : Type} (a1 a2 b1 b2 : α) (F : α → Prop) (P D U : α → α → Prop) :
    ((∀ u ∈ [a1, a2], ∀ v ∈ [b1, b2], F u ∧ F v ∧ P u v ∧ D u v) ∧
        ∀ u ∈ [a1, a2], ∀ v ∈ [b1, b2], F u ∧ F v ∧ P u v ∧ U u v) ↔
      F a1 ∧ F a2 ∧ F b1 ∧ F b2 ∧ ∀ u ∈ [a1, a2], ∀ v ∈ [b1, b2], P u v ∧ D u v ∧ U u v := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
  tauto

/-- The conditions on the four corners of a quotient, for the lower and the upper endpoint,
gathered by endpoint and by corner. -/
theorem corners_div_iff {α : Type} (a1 a2 b1 b2 : α) (F N : α → Prop) (P D U : α → α → Prop) :
    ((∀ u ∈ [a1, a2], ∀ v ∈ [b1, b2], F u ∧ F v ∧ N v ∧ P u v ∧ D u v) ∧
        ∀ u ∈ [a1, a2], ∀ v ∈ [b1, b2], F u ∧ F v ∧ N v ∧ P u v ∧ U u v) ↔
      F a1 ∧ F a2 ∧ F b1 ∧ F b2 ∧ N b1 ∧ N b2 ∧
        ∀ u ∈ [a1, a2], ∀ v ∈ [b1, b2], P u v ∧ D u v ∧ U u v := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
  tauto

theorem mulEnd_status (up : Bool) (a b : Interval) :
    (mulEnd up a b).status = 0 ↔ ∀ u ∈ [a.lo, a.hi], ∀ v ∈ [b.lo, b.hi],
      Finite u.toBits ∧ Finite v.toBits ∧ Finite (Wasm.IEEE64.mul u.toBits v.toBits) ∧
        Finite (F64Outward.neighbor up (Wasm.IEEE64.mul u.toBits v.toBits)) := by
  unfold mulEnd
  rw [extreme_status, (outMul_outward up a.lo b.lo).1, (outMul_outward up a.lo b.hi).1,
    (outMul_outward up a.hi b.lo).1, (outMul_outward up a.hi b.hi).1]
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    and_assoc, iff_self]

theorem mulEnd_lower {a b : Interval} (h : (mulEnd false a b).status = 0) :
    Finite (mulEnd false a b).value.toBits ∧
      value (mulEnd false a b).value.toBits =
        min (min (value (nextDown (Wasm.IEEE64.mul a.lo.toBits b.lo.toBits)))
            (value (nextDown (Wasm.IEEE64.mul a.lo.toBits b.hi.toBits))))
          (min (value (nextDown (Wasm.IEEE64.mul a.hi.toBits b.lo.toBits)))
            (value (nextDown (Wasm.IEEE64.mul a.hi.toBits b.hi.toBits)))) ∧
      ∀ x y, value a.lo.toBits ≤ x → x ≤ value a.hi.toBits → value b.lo.toBits ≤ y →
        y ≤ value b.hi.toBits → value (mulEnd false a b).value.toBits ≤ x * y := by
  unfold mulEnd at h ⊢
  obtain ⟨l1, l2, l3, l4⟩ := extreme_accepted h
  obtain ⟨fl1, bl1⟩ := lower (outMul_accepted l1).2.2
  obtain ⟨fl2, bl2⟩ := lower (outMul_accepted l2).2.2
  obtain ⟨fl3, bl3⟩ := lower (outMul_accepted l3).2.2
  obtain ⟨fl4, bl4⟩ := lower (outMul_accepted l4).2.2
  obtain ⟨fL, vL⟩ := extreme_lower h fl1 fl2 fl3 fl4
  refine ⟨fL, ?_, fun x y hx1 hx2 hy1 hy2 => ?_⟩
  · rw [vL, (outMul_outward false a.lo b.lo).lower.1.2 l1,
      (outMul_outward false a.lo b.hi).lower.1.2 l2, (outMul_outward false a.hi b.lo).lower.1.2 l3,
      (outMul_outward false a.hi b.hi).lower.1.2 l4]
  · rw [vL]
    exact le_mul_of_corners hx1 hx2 hy1 hy2
      (((min_le_left _ _).trans (min_le_left _ _)).trans bl1)
      (((min_le_left _ _).trans (min_le_right _ _)).trans bl2)
      (((min_le_right _ _).trans (min_le_left _ _)).trans bl3)
      (((min_le_right _ _).trans (min_le_right _ _)).trans bl4)

theorem mulEnd_upper {a b : Interval} (h : (mulEnd true a b).status = 0) :
    Finite (mulEnd true a b).value.toBits ∧
      value (mulEnd true a b).value.toBits =
        max (max (value (nextUp (Wasm.IEEE64.mul a.lo.toBits b.lo.toBits)))
            (value (nextUp (Wasm.IEEE64.mul a.lo.toBits b.hi.toBits))))
          (max (value (nextUp (Wasm.IEEE64.mul a.hi.toBits b.lo.toBits)))
            (value (nextUp (Wasm.IEEE64.mul a.hi.toBits b.hi.toBits)))) ∧
      ∀ x y, value a.lo.toBits ≤ x → x ≤ value a.hi.toBits → value b.lo.toBits ≤ y →
        y ≤ value b.hi.toBits → x * y ≤ value (mulEnd true a b).value.toBits := by
  unfold mulEnd at h ⊢
  obtain ⟨u1, u2, u3, u4⟩ := extreme_accepted h
  obtain ⟨fu1, bu1⟩ := upper (outMul_accepted u1).2.2
  obtain ⟨fu2, bu2⟩ := upper (outMul_accepted u2).2.2
  obtain ⟨fu3, bu3⟩ := upper (outMul_accepted u3).2.2
  obtain ⟨fu4, bu4⟩ := upper (outMul_accepted u4).2.2
  obtain ⟨fU, vU⟩ := extreme_upper h fu1 fu2 fu3 fu4
  refine ⟨fU, ?_, fun x y hx1 hx2 hy1 hy2 => ?_⟩
  · rw [vU, (outMul_outward true a.lo b.lo).upper.1.2 u1,
      (outMul_outward true a.lo b.hi).upper.1.2 u2, (outMul_outward true a.hi b.lo).upper.1.2 u3,
      (outMul_outward true a.hi b.hi).upper.1.2 u4]
  · rw [vU]
    exact mul_le_of_corners hx1 hx2 hy1 hy2
      (bu1.trans ((le_max_left _ _).trans (le_max_left _ _)))
      (bu2.trans ((le_max_right _ _).trans (le_max_left _ _)))
      (bu3.trans ((le_max_left _ _).trans (le_max_right _ _)))
      (bu4.trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem mul_status (a b : Interval) :
    (mul a b).status = 0 ↔ a.status = 0 ∧ b.status = 0 ∧ Finite a.lo.toBits ∧
      Finite a.hi.toBits ∧ Finite b.lo.toBits ∧ Finite b.hi.toBits ∧
      ∀ u ∈ [a.lo, a.hi], ∀ v ∈ [b.lo, b.hi], Finite (Wasm.IEEE64.mul u.toBits v.toBits) ∧
        Finite (nextDown (Wasm.IEEE64.mul u.toBits v.toBits)) ∧
        Finite (nextUp (Wasm.IEEE64.mul u.toBits v.toBits)) := by
  unfold mul
  rw [join_status, mulEnd_status, mulEnd_status]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    corners_iff a.lo a.hi b.lo b.hi (fun u => Finite u.toBits)
      (fun u v => Finite (Wasm.IEEE64.mul u.toBits v.toBits))
      (fun u v => Finite (nextDown (Wasm.IEEE64.mul u.toBits v.toBits)))
      (fun u v => Finite (nextUp (Wasm.IEEE64.mul u.toBits v.toBits)))

theorem divEnd_status (up : Bool) (a b : Interval) :
    (divEnd up a b).status = 0 ↔ ∀ u ∈ [a.lo, a.hi], ∀ v ∈ [b.lo, b.hi],
      Finite u.toBits ∧ Finite v.toBits ∧ value v.toBits ≠ 0 ∧
        Finite (Wasm.IEEE64.div u.toBits v.toBits) ∧
        Finite (F64Outward.neighbor up (Wasm.IEEE64.div u.toBits v.toBits)) := by
  unfold divEnd
  rw [extreme_status, (outDiv_outward up a.lo b.lo).1, (outDiv_outward up a.lo b.hi).1,
    (outDiv_outward up a.hi b.lo).1, (outDiv_outward up a.hi b.hi).1]
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    and_assoc, iff_self]

theorem divEnd_lower {a b : Interval} (h : (divEnd false a b).status = 0) :
    Finite (divEnd false a b).value.toBits ∧
      value (divEnd false a b).value.toBits =
        min (min (value (nextDown (Wasm.IEEE64.div a.lo.toBits b.lo.toBits)))
            (value (nextDown (Wasm.IEEE64.div a.lo.toBits b.hi.toBits))))
          (min (value (nextDown (Wasm.IEEE64.div a.hi.toBits b.lo.toBits)))
            (value (nextDown (Wasm.IEEE64.div a.hi.toBits b.hi.toBits)))) ∧
      ((0 < value b.lo.toBits ∨ value b.hi.toBits < 0) →
        ∀ x y, value a.lo.toBits ≤ x → x ≤ value a.hi.toBits → value b.lo.toBits ≤ y →
          y ≤ value b.hi.toBits → value (divEnd false a b).value.toBits ≤ x / y) := by
  unfold divEnd at h ⊢
  obtain ⟨l1, l2, l3, l4⟩ := extreme_accepted h
  obtain ⟨fl1, bl1⟩ := lower (outDiv_accepted l1).2.2.2
  obtain ⟨fl2, bl2⟩ := lower (outDiv_accepted l2).2.2.2
  obtain ⟨fl3, bl3⟩ := lower (outDiv_accepted l3).2.2.2
  obtain ⟨fl4, bl4⟩ := lower (outDiv_accepted l4).2.2.2
  obtain ⟨fL, vL⟩ := extreme_lower h fl1 fl2 fl3 fl4
  refine ⟨fL, ?_, fun hz x y hx1 hx2 hy1 hy2 => ?_⟩
  · rw [vL, (outDiv_outward false a.lo b.lo).lower.1.2 l1,
      (outDiv_outward false a.lo b.hi).lower.1.2 l2, (outDiv_outward false a.hi b.lo).lower.1.2 l3,
      (outDiv_outward false a.hi b.hi).lower.1.2 l4]
  · rw [vL]
    exact le_div_of_corners hx1 hx2 hy1 hy2 hz
      (((min_le_left _ _).trans (min_le_left _ _)).trans bl1)
      (((min_le_left _ _).trans (min_le_right _ _)).trans bl2)
      (((min_le_right _ _).trans (min_le_left _ _)).trans bl3)
      (((min_le_right _ _).trans (min_le_right _ _)).trans bl4)

theorem divEnd_upper {a b : Interval} (h : (divEnd true a b).status = 0) :
    Finite (divEnd true a b).value.toBits ∧
      value (divEnd true a b).value.toBits =
        max (max (value (nextUp (Wasm.IEEE64.div a.lo.toBits b.lo.toBits)))
            (value (nextUp (Wasm.IEEE64.div a.lo.toBits b.hi.toBits))))
          (max (value (nextUp (Wasm.IEEE64.div a.hi.toBits b.lo.toBits)))
            (value (nextUp (Wasm.IEEE64.div a.hi.toBits b.hi.toBits)))) ∧
      ((0 < value b.lo.toBits ∨ value b.hi.toBits < 0) →
        ∀ x y, value a.lo.toBits ≤ x → x ≤ value a.hi.toBits → value b.lo.toBits ≤ y →
          y ≤ value b.hi.toBits → x / y ≤ value (divEnd true a b).value.toBits) := by
  unfold divEnd at h ⊢
  obtain ⟨u1, u2, u3, u4⟩ := extreme_accepted h
  obtain ⟨fu1, bu1⟩ := upper (outDiv_accepted u1).2.2.2
  obtain ⟨fu2, bu2⟩ := upper (outDiv_accepted u2).2.2.2
  obtain ⟨fu3, bu3⟩ := upper (outDiv_accepted u3).2.2.2
  obtain ⟨fu4, bu4⟩ := upper (outDiv_accepted u4).2.2.2
  obtain ⟨fU, vU⟩ := extreme_upper h fu1 fu2 fu3 fu4
  refine ⟨fU, ?_, fun hz x y hx1 hx2 hy1 hy2 => ?_⟩
  · rw [vU, (outDiv_outward true a.lo b.lo).upper.1.2 u1,
      (outDiv_outward true a.lo b.hi).upper.1.2 u2, (outDiv_outward true a.hi b.lo).upper.1.2 u3,
      (outDiv_outward true a.hi b.hi).upper.1.2 u4]
  · rw [vU]
    exact div_le_of_corners hx1 hx2 hy1 hy2 hz
      (bu1.trans ((le_max_left _ _).trans (le_max_left _ _)))
      (bu2.trans ((le_max_right _ _).trans (le_max_left _ _)))
      (bu3.trans ((le_max_left _ _).trans (le_max_right _ _)))
      (bu4.trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem divCore_status (a b : Interval) :
    (divCore a b).status = 0 ↔ a.status = 0 ∧ b.status = 0 ∧ Finite a.lo.toBits ∧
      Finite a.hi.toBits ∧ Finite b.lo.toBits ∧ Finite b.hi.toBits ∧ value b.lo.toBits ≠ 0 ∧
      value b.hi.toBits ≠ 0 ∧
      ∀ u ∈ [a.lo, a.hi], ∀ v ∈ [b.lo, b.hi], Finite (Wasm.IEEE64.div u.toBits v.toBits) ∧
        Finite (nextDown (Wasm.IEEE64.div u.toBits v.toBits)) ∧
        Finite (nextUp (Wasm.IEEE64.div u.toBits v.toBits)) := by
  unfold divCore
  rw [join_status, divEnd_status, divEnd_status]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    corners_div_iff a.lo a.hi b.lo b.hi (fun u => Finite u.toBits) (fun v => value v.toBits ≠ 0)
      (fun u v => Finite (Wasm.IEEE64.div u.toBits v.toBits))
      (fun u v => Finite (nextDown (Wasm.IEEE64.div u.toBits v.toBits)))
      (fun u v => Finite (nextUp (Wasm.IEEE64.div u.toBits v.toBits)))

theorem divCore_values {a b : Interval} (h : (divCore a b).status = 0) :
    Finite (divCore a b).lo.toBits ∧ Finite (divCore a b).hi.toBits ∧
      value (divCore a b).lo.toBits =
        min (min (value (nextDown (Wasm.IEEE64.div a.lo.toBits b.lo.toBits)))
            (value (nextDown (Wasm.IEEE64.div a.lo.toBits b.hi.toBits))))
          (min (value (nextDown (Wasm.IEEE64.div a.hi.toBits b.lo.toBits)))
            (value (nextDown (Wasm.IEEE64.div a.hi.toBits b.hi.toBits)))) ∧
      value (divCore a b).hi.toBits =
        max (max (value (nextUp (Wasm.IEEE64.div a.lo.toBits b.lo.toBits)))
            (value (nextUp (Wasm.IEEE64.div a.lo.toBits b.hi.toBits))))
          (max (value (nextUp (Wasm.IEEE64.div a.hi.toBits b.lo.toBits)))
            (value (nextUp (Wasm.IEEE64.div a.hi.toBits b.hi.toBits)))) := by
  unfold divCore at h ⊢
  obtain ⟨-, sl, sh⟩ := (join_status _ _ _).mp h
  obtain ⟨fl, vl, -⟩ := divEnd_lower sl
  obtain ⟨fu, vu, -⟩ := divEnd_upper sh
  rw [join_eq h]
  exact ⟨fl, fu, vl, vu⟩

theorem div_eq_divCore {a b : Interval} (h : (div a b).status = 0) : div a b = divCore a b := by
  unfold div at h ⊢
  by_cases h1 : (0 : Float) < b.lo
  · rw [ite_eq_left h1]
  · by_cases h2 : b.hi < 0
    · rw [ite_eq_right h1, ite_eq_left h2]
    · rw [ite_eq_right h1, ite_eq_right h2] at h
      exact absurd h (by decide)

theorem div_status (a b : Interval) :
    (div a b).status = 0 ↔
      (0 < value b.lo.toBits ∨ value b.hi.toBits < 0) ∧ (divCore a b).status = 0 := by
  constructor
  · intro h
    have hc : (divCore a b).status = 0 := by rw [← div_eq_divCore h]; exact h
    obtain ⟨-, -, -, -, fl, fh, -⟩ := (divCore_status a b).mp hc
    refine ⟨?_, hc⟩
    unfold div at h
    by_cases h1 : (0 : Float) < b.lo
    · left
      have := (lt_iff_value zero_value.1 fl).mp h1
      rwa [zero_value.2] at this
    · by_cases h2 : b.hi < 0
      · right
        have := (lt_iff_value fh zero_value.1).mp h2
        rwa [zero_value.2] at this
      · rw [ite_eq_right h1, ite_eq_right h2] at h
        exact absurd h (by decide)
  · rintro ⟨hz, hc⟩
    obtain ⟨-, -, -, -, fl, fh, -⟩ := (divCore_status a b).mp hc
    unfold div
    by_cases h1 : (0 : Float) < b.lo
    · rw [ite_eq_left h1]
      exact hc
    · have h2 : b.hi < 0 := by
        rcases hz with hz | hz
        · exact absurd ((lt_iff_value zero_value.1 fl).mpr (by rw [zero_value.2]; exact hz)) h1
        · exact (lt_iff_value fh zero_value.1).mpr (by rw [zero_value.2]; exact hz)
      rw [ite_eq_right h1, ite_eq_left h2]
      exact hc

theorem make_eq_of {lo hi : Float} (f1 : Finite lo.toBits) (f2 : Finite hi.toBits)
    (hle : value lo.toBits ≤ value hi.toBits) : make lo hi = ⟨0, lo, hi⟩ := by
  have hb : (finite lo && finite hi) = true := by
    simp only [Bool.and_eq_true, finite_iff]
    exact ⟨f1, f2⟩
  unfold make
  rw [ite_eq_left hb, ite_eq_left ((le_iff_value f1 f2).mpr hle)]

theorem point_eq_of {x : Float} (f : Finite x.toBits) : point x = ⟨0, x, x⟩ := by
  unfold point
  rw [ite_eq_left ((finite_iff x).mpr f)]

theorem neg_status (a : Interval) : (neg a).status = 0 ↔ a.status = 0 := by
  refine ⟨fun h => (neg_sound h).1, fun hs => ?_⟩
  unfold neg
  rw [ite_eq_left (beq_iff_eq.mpr hs)]

theorem neg_fields {a : Interval} (h : (neg a).status = 0) :
    (neg a).lo = -a.hi ∧ (neg a).hi = -a.lo := by
  unfold neg
  rw [ite_eq_left (beq_iff_eq.mpr (neg_sound h).1)]
  exact ⟨rfl, rfl⟩

theorem abs_status (a : Interval) : (abs a).status = 0 ↔ a.status = 0 := by
  refine ⟨fun h => (abs_sound h).1, fun hs => ?_⟩
  unfold abs
  rw [ite_eq_left (beq_iff_eq.mpr hs)]
  split_ifs
  · exact hs
  · rfl
  · rfl

theorem abs_fields {a : Interval} (h : (abs a).status = 0) :
    if 0 ≤ a.lo then (abs a).lo = a.lo ∧ (abs a).hi = a.hi
    else if a.hi ≤ 0 then (abs a).lo = -a.hi ∧ (abs a).hi = -a.lo
    else (abs a).lo = 0 ∧ (abs a).hi = max (-a.lo) a.hi := by
  unfold abs
  rw [ite_eq_left (beq_iff_eq.mpr (abs_sound h).1)]
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem clamp_status (a : Interval) (lo hi : Float) :
    (clamp a lo hi).status = 0 ↔ a.status = 0 ∧ Finite lo.toBits ∧ Finite hi.toBits := by
  have e : (a.status == 0 && finite lo && finite hi) = true ↔
      a.status = 0 ∧ Finite lo.toBits ∧ Finite hi.toBits := by
    simp only [Bool.and_eq_true, beq_iff_eq, finite_iff, and_assoc, iff_self]
  rw [← e]
  unfold clamp
  by_cases hc : (a.status == 0 && finite lo && finite hi) = true
  · rw [ite_eq_left hc]
    exact iff_of_true rfl hc
  · rw [ite_eq_right hc]
    exact iff_of_false (by decide) hc

theorem clamp_fields {a : Interval} {lo hi : Float} (h : (clamp a lo hi).status = 0) :
    (clamp a lo hi).lo = max a.lo lo ∧ (clamp a lo hi).hi = min a.hi hi := by
  unfold clamp at h ⊢
  by_cases hc : (a.status == 0 && finite lo && finite hi) = true
  · rw [ite_eq_left hc]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hc] at h
    exact absurd h (by decide)

/-! ### Exports -/

theorem fmin_export :
    ({ name := "fmin", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem fmax_export :
    ({ name := "fmax", funcIdx := 13 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem make_export :
    ({ name := "make", funcIdx := 14 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem point_export :
    ({ name := "point", funcIdx := 15 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem join_export :
    ({ name := "join", funcIdx := 16 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem add_export :
    ({ name := "add", funcIdx := 17 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sub_export :
    ({ name := "sub", funcIdx := 18 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem neg_export :
    ({ name := "neg", funcIdx := 19 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem extreme_export :
    ({ name := "extreme", funcIdx := 20 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem mulEnd_export :
    ({ name := "mulEnd", funcIdx := 21 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem mul_export :
    ({ name := "mul", funcIdx := 22 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem divEnd_export :
    ({ name := "divEnd", funcIdx := 23 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem divCore_export :
    ({ name := "divCore", funcIdx := 24 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem div_export :
    ({ name := "div", funcIdx := 25 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sqrt_export :
    ({ name := "sqrt", funcIdx := 26 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem abs_export :
    ({ name := "abs", funcIdx := 27 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem clamp_export :
    ({ name := "clamp", funcIdx := 28 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem outward2_export :
    ({ name := "outward2", funcIdx := 29 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem increasing_export :
    ({ name := "increasing", funcIdx := 30 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem decreasing_export :
    ({ name := "decreasing", funcIdx := 31 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-! ### Master theorems -/

/-- The export `fmin`, called on two floats, returns Lean's `min` of them, which compares by
IEEE 754 `≤`; for finite floats the result is finite and its value is the smaller value. -/
theorem fmin_master :
    Verified.Master compiled.module compiled.tables "fmin" compiled.fmin.bound (fun _ => True)
      (fun (x : Float × Float) (y : Float) => y = min x.1 x.2 ∧
        (Finite x.1.toBits → Finite x.2.toBits →
          Finite y.toBits ∧ value y.toBits = min (value x.1.toBits) (value x.2.toBits))) :=
  .of_trapFree (.ofA compiled.fmin.trapFree) nofun fmin_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ _ _ _ => ⟨rfl, fun h1 h2 => fmin_value h1 h2⟩

#print axioms fmin_master

/-- The export `fmax`, called on two floats, returns Lean's `max` of them, which compares by
IEEE 754 `≤`; for finite floats the result is finite and its value is the larger value. -/
theorem fmax_master :
    Verified.Master compiled.module compiled.tables "fmax" compiled.fmax.bound (fun _ => True)
      (fun (x : Float × Float) (y : Float) => y = max x.1 x.2 ∧
        (Finite x.1.toBits → Finite x.2.toBits →
          Finite y.toBits ∧ value y.toBits = max (value x.1.toBits) (value x.2.toBits))) :=
  .of_trapFree (.ofA compiled.fmax.trapFree) nofun fmax_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ _ _ _ => ⟨rfl, fun h1 h2 => fmax_value h1 h2⟩

#print axioms fmax_master

/-- The export `make`, called on floats `lo` and `hi`, accepts exactly when both are finite and
the value of `lo` is at most the value of `hi`, and then returns the interval with endpoints `lo`
and `hi`, which contains every real between their values. -/
theorem make_master :
    Verified.Master compiled.module compiled.tables "make" compiled.make.bound (fun _ => True)
      (fun (x : Float × Float) (r : Interval) =>
        (r.status = 0 ↔
          Finite x.1.toBits ∧ Finite x.2.toBits ∧ value x.1.toBits ≤ value x.2.toBits) ∧
        (r.status = 0 → r.lo = x.1 ∧ r.hi = x.2) ∧
        (r.status = 0 → ∀ t, value x.1.toBits ≤ t → t ≤ value x.2.toBits → Contains r t)) :=
  .of_trapFree (.ofA compiled.make.trapFree) nofun make_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      refine ⟨⟨fun h => ?_, fun ⟨f1, f2, hle⟩ => by rw [make_eq_of f1 f2 hle]⟩, fun h => ?_,
        fun h => (make_sound h).2.2.2⟩
      · obtain ⟨f1, f2, hle, -⟩ := make_sound h
        exact ⟨f1, f2, hle⟩
      · obtain ⟨f1, f2, hle, -⟩ := make_sound h
        rw [make_eq_of f1 f2 hle]
        exact ⟨rfl, rfl⟩

#print axioms make_master

/-- The export `point`, called on a float `x`, accepts exactly when `x` is finite, and then
returns the interval with both endpoints `x`, which contains the value of `x`. -/
theorem point_master :
    Verified.Master compiled.module compiled.tables "point" compiled.point.bound (fun _ => True)
      (fun (x : Float) (r : Interval) =>
        (r.status = 0 ↔ Finite x.toBits) ∧ (r.status = 0 → r.lo = x ∧ r.hi = x) ∧
        (r.status = 0 → Contains r (value x.toBits))) :=
  .of_trapFree (.ofA compiled.point.trapFree) nofun point_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      refine ⟨⟨fun h => (point_sound h).1, fun f => by rw [point_eq_of f]⟩, fun h => ?_,
        fun h => (point_sound h).2⟩
      rw [point_eq_of (point_sound h).1]
      exact ⟨rfl, rfl⟩

#print axioms point_master

/-- The export `join`, called on a flag `ok` and checked values `l` and `h`, accepts exactly when
`ok` holds and `l` and `h` are accepted, and then returns the interval with endpoints the values
of `l` and `h`. -/
theorem join_master :
    Verified.Master compiled.module compiled.tables "join" compiled.join.bound (fun _ => True)
      (fun (x : Bool × Checked × Checked) (r : Interval) =>
        (r.status = 0 ↔ x.1 = true ∧ x.2.1.status = 0 ∧ x.2.2.status = 0) ∧
        (r.status = 0 → r.lo = x.2.1.value ∧ r.hi = x.2.2.value)) :=
  .of_trapFree (.ofA compiled.join.trapFree) nofun join_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => ⟨join_status x.1 x.2.1 x.2.2, join_fields⟩

#print axioms join_master

/-- The export `add`, called on intervals `a` and `b`, accepts exactly when both are accepted, their
endpoints are finite, and the IEEE 754 sums of the lower and of the upper endpoints are finite and
stay finite one step outward; it then returns those sums one step down and one step up, an
interval that contains `x + y` for every `x` in `a` and `y` in `b`. -/
theorem add_master :
    Verified.Master compiled.module compiled.tables "add" compiled.add.bound (fun _ => True)
      (fun (x : Interval × Interval) (r : Interval) =>
        let a := x.1
        let b := x.2
        let l := Wasm.IEEE64.add a.lo.toBits b.lo.toBits
        let h := Wasm.IEEE64.add a.hi.toBits b.hi.toBits
        (r.status = 0 ↔ a.status = 0 ∧ b.status = 0 ∧ Finite a.lo.toBits ∧ Finite b.lo.toBits ∧
          Finite l ∧ Finite (nextDown l) ∧ Finite a.hi.toBits ∧ Finite b.hi.toBits ∧ Finite h ∧
          Finite (nextUp h)) ∧
        (r.status = 0 → r.lo.toBits = nextDown l ∧ r.hi.toBits = nextUp h) ∧
        (r.status = 0 → ∀ s t, Contains a s → Contains b t → Contains r (s + t))) :=
  .of_trapFree (.ofA compiled.add.trapFree) nofun add_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      obtain ⟨hs, hv⟩ := join_endpoints (ok := x.1.status == 0 && x.2.status == 0)
        (outAdd_outward false x.1.lo x.2.lo).lower.1 (outAdd_outward true x.1.hi x.2.hi).upper.1
      simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hs
      exact ⟨hs, hv, fun h => (add_sound h).2.2⟩

#print axioms add_master

/-- The export `sub`, called on intervals `a` and `b`, accepts exactly when both are accepted,
their endpoints are finite, and the IEEE 754 differences `a.lo - b.hi` and `a.hi - b.lo` are
finite and stay finite one step outward; it then returns those differences one step down and one
step up, an interval that contains `x - y` for every `x` in `a` and `y` in `b`. -/
theorem sub_master :
    Verified.Master compiled.module compiled.tables "sub" compiled.sub.bound (fun _ => True)
      (fun (x : Interval × Interval) (r : Interval) =>
        let a := x.1
        let b := x.2
        let l := Wasm.IEEE64.sub a.lo.toBits b.hi.toBits
        let h := Wasm.IEEE64.sub a.hi.toBits b.lo.toBits
        (r.status = 0 ↔ a.status = 0 ∧ b.status = 0 ∧ Finite a.lo.toBits ∧ Finite b.hi.toBits ∧
          Finite l ∧ Finite (nextDown l) ∧ Finite a.hi.toBits ∧ Finite b.lo.toBits ∧ Finite h ∧
          Finite (nextUp h)) ∧
        (r.status = 0 → r.lo.toBits = nextDown l ∧ r.hi.toBits = nextUp h) ∧
        (r.status = 0 → ∀ s t, Contains a s → Contains b t → Contains r (s - t))) :=
  .of_trapFree (.ofA compiled.sub.trapFree) nofun sub_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      obtain ⟨hs, hv⟩ := join_endpoints (ok := x.1.status == 0 && x.2.status == 0)
        (outSub_outward false x.1.lo x.2.hi).lower.1 (outSub_outward true x.1.hi x.2.lo).upper.1
      simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hs
      exact ⟨hs, hv, fun h => (sub_sound h).2.2⟩

#print axioms sub_master

/-- The export `neg`, called on an interval `a`, accepts exactly when `a` is accepted, and then
returns the interval from `-a.hi` to `-a.lo`, which contains `-x` for every `x` in `a`. -/
theorem neg_master :
    Verified.Master compiled.module compiled.tables "neg" compiled.neg.bound (fun _ => True)
      (fun (a : Interval) (r : Interval) =>
        (r.status = 0 ↔ a.status = 0) ∧ (r.status = 0 → r.lo = -a.hi ∧ r.hi = -a.lo) ∧
        (r.status = 0 → ∀ t, Contains a t → Contains r (-t))) :=
  .of_trapFree (.ofA compiled.neg.trapFree) nofun neg_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ a _ _ => ⟨neg_status a, neg_fields, fun h => (neg_sound h).2⟩

#print axioms neg_master

/-- The export `extreme`, called on a direction `up` and checked values `p`, `q`, `r`, and `s`,
accepts exactly when all four are accepted, and then returns Lean's `max` of their values for `up`
and `min` otherwise; when the four values are finite, the result is finite and its value is the
greatest or the least of their values. -/
theorem extreme_master :
    Verified.Master compiled.module compiled.tables "extreme" compiled.extreme.bound
      (fun _ => True)
      (fun (x : Bool × Checked × Checked × Checked × Checked) (c : Checked) =>
        let up := x.1
        let p := x.2.1
        let q := x.2.2.1
        let r := x.2.2.2.1
        let s := x.2.2.2.2
        (c.status = 0 ↔ p.status = 0 ∧ q.status = 0 ∧ r.status = 0 ∧ s.status = 0) ∧
        (c.status = 0 → c.value =
          if up then max (max p.value q.value) (max r.value s.value)
          else min (min p.value q.value) (min r.value s.value)) ∧
        (c.status = 0 → Finite p.value.toBits → Finite q.value.toBits → Finite r.value.toBits →
          Finite s.value.toBits → Finite c.value.toBits ∧ value c.value.toBits =
            if up then max (max (value p.value.toBits) (value q.value.toBits))
              (max (value r.value.toBits) (value s.value.toBits))
            else min (min (value p.value.toBits) (value q.value.toBits))
              (min (value r.value.toBits) (value s.value.toBits)))) :=
  .of_trapFree (.ofA compiled.extreme.trapFree) nofun extreme_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ =>
      ⟨extreme_status x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2, extreme_value, extreme_values⟩

#print axioms extreme_master

/-- The export `mulEnd`, called on a direction `up` and intervals `a` and `b`, accepts exactly
when, for every endpoint `u` of `a` and `v` of `b`, `u`, `v`, the IEEE 754 product, and the
product one step up for `up` or down otherwise are finite; its value is then the greatest of those
moved products for `up` and the least otherwise, and it bounds `x * y` from above for `up` and
from below otherwise for every `x` between the values of the endpoints of `a` and `y` between those
of `b`. -/
theorem mulEnd_master :
    Verified.Master compiled.module compiled.tables "mulEnd" compiled.mulEnd.bound
      (fun _ => True)
      (fun (x : Bool × Interval × Interval) (c : Checked) =>
        let up := x.1
        let a := x.2.1
        let b := x.2.2
        let m := fun u v : Float => Wasm.IEEE64.mul u.toBits v.toBits
        let w := fun u v : Float => value (F64Outward.neighbor up (m u v))
        (c.status = 0 ↔ ∀ u ∈ [a.lo, a.hi], ∀ v ∈ [b.lo, b.hi],
          Finite u.toBits ∧ Finite v.toBits ∧ Finite (m u v) ∧
            Finite (F64Outward.neighbor up (m u v))) ∧
        (c.status = 0 → Finite c.value.toBits ∧ value c.value.toBits =
          if up then max (max (w a.lo b.lo) (w a.lo b.hi)) (max (w a.hi b.lo) (w a.hi b.hi))
          else min (min (w a.lo b.lo) (w a.lo b.hi)) (min (w a.hi b.lo) (w a.hi b.hi))) ∧
        (c.status = 0 → ∀ s t, value a.lo.toBits ≤ s → s ≤ value a.hi.toBits →
          value b.lo.toBits ≤ t → t ≤ value b.hi.toBits →
          if up then s * t ≤ value c.value.toBits else value c.value.toBits ≤ s * t)) :=
  .of_trapFree (.ofA compiled.mulEnd.trapFree) nofun mulEnd_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      obtain ⟨up, a, b⟩ := x
      refine ⟨mulEnd_status up a b, ?_⟩
      cases up
      · exact ⟨fun h => ⟨(mulEnd_lower h).1, (mulEnd_lower h).2.1⟩, fun h => (mulEnd_lower h).2.2⟩
      · exact ⟨fun h => ⟨(mulEnd_upper h).1, (mulEnd_upper h).2.1⟩, fun h => (mulEnd_upper h).2.2⟩

#print axioms mulEnd_master

/-- The export `mul`, called on intervals `a` and `b`, accepts exactly when both are accepted,
their endpoints are finite, and every IEEE 754 product of an endpoint of `a` and an endpoint of
`b` is finite and stays finite one step down and one step up; the value of the result's lower
endpoint is then the least of those products moved one step down, the value of its upper endpoint
the greatest of them moved one step up, and the result contains `x * y` for every `x` in `a` and
`y` in `b`. -/
theorem mul_master :
    Verified.Master compiled.module compiled.tables "mul" compiled.mul.bound (fun _ => True)
      (fun (x : Interval × Interval) (r : Interval) =>
        let a := x.1
        let b := x.2
        let m := fun u v : Float => Wasm.IEEE64.mul u.toBits v.toBits
        (r.status = 0 ↔ a.status = 0 ∧ b.status = 0 ∧ Finite a.lo.toBits ∧ Finite a.hi.toBits ∧
          Finite b.lo.toBits ∧ Finite b.hi.toBits ∧ ∀ u ∈ [a.lo, a.hi], ∀ v ∈ [b.lo, b.hi],
            Finite (m u v) ∧ Finite (nextDown (m u v)) ∧ Finite (nextUp (m u v))) ∧
        (r.status = 0 → Finite r.lo.toBits ∧ Finite r.hi.toBits ∧
          value r.lo.toBits =
            min (min (value (nextDown (m a.lo b.lo))) (value (nextDown (m a.lo b.hi))))
              (min (value (nextDown (m a.hi b.lo))) (value (nextDown (m a.hi b.hi)))) ∧
          value r.hi.toBits =
            max (max (value (nextUp (m a.lo b.lo))) (value (nextUp (m a.lo b.hi))))
              (max (value (nextUp (m a.hi b.lo))) (value (nextUp (m a.hi b.hi))))) ∧
        (r.status = 0 → ∀ s t, Contains a s → Contains b t → Contains r (s * t))) :=
  .of_trapFree (.ofA compiled.mul.trapFree) nofun mul_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      refine ⟨mul_status x.1 x.2, fun h => ?_, fun h => (mul_sound h).2.2⟩
      unfold mul at h ⊢
      obtain ⟨-, sl, sh⟩ := (join_status _ _ _).mp h
      obtain ⟨fl, vl, -⟩ := mulEnd_lower sl
      obtain ⟨fu, vu, -⟩ := mulEnd_upper sh
      rw [join_eq h]
      exact ⟨fl, fu, vl, vu⟩

#print axioms mul_master

/-- The export `divEnd`, called on a direction `up` and intervals `a` and `b`, accepts exactly
when, for every endpoint `u` of `a` and `v` of `b`, `u` and `v` are finite, the value of `v` is
not zero, and the IEEE 754 quotient and the quotient one step up for `up` or down otherwise are
finite; its value is then the greatest of those moved quotients for `up` and the least otherwise,
and when the values of the endpoints of `b` lie on one side of zero it bounds `x / y` from above
for `up` and from below otherwise for every `x` between the values of the endpoints of `a` and `y`
between those of `b`. -/
theorem divEnd_master :
    Verified.Master compiled.module compiled.tables "divEnd" compiled.divEnd.bound
      (fun _ => True)
      (fun (x : Bool × Interval × Interval) (c : Checked) =>
        let up := x.1
        let a := x.2.1
        let b := x.2.2
        let q := fun u v : Float => Wasm.IEEE64.div u.toBits v.toBits
        let w := fun u v : Float => value (F64Outward.neighbor up (q u v))
        (c.status = 0 ↔ ∀ u ∈ [a.lo, a.hi], ∀ v ∈ [b.lo, b.hi],
          Finite u.toBits ∧ Finite v.toBits ∧ value v.toBits ≠ 0 ∧ Finite (q u v) ∧
            Finite (F64Outward.neighbor up (q u v))) ∧
        (c.status = 0 → Finite c.value.toBits ∧ value c.value.toBits =
          if up then max (max (w a.lo b.lo) (w a.lo b.hi)) (max (w a.hi b.lo) (w a.hi b.hi))
          else min (min (w a.lo b.lo) (w a.lo b.hi)) (min (w a.hi b.lo) (w a.hi b.hi))) ∧
        (c.status = 0 → (0 < value b.lo.toBits ∨ value b.hi.toBits < 0) →
          ∀ s t, value a.lo.toBits ≤ s → s ≤ value a.hi.toBits →
          value b.lo.toBits ≤ t → t ≤ value b.hi.toBits →
          if up then s / t ≤ value c.value.toBits else value c.value.toBits ≤ s / t)) :=
  .of_trapFree (.ofA compiled.divEnd.trapFree) nofun divEnd_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      obtain ⟨up, a, b⟩ := x
      refine ⟨divEnd_status up a b, ?_⟩
      cases up
      · exact ⟨fun h => ⟨(divEnd_lower h).1, (divEnd_lower h).2.1⟩, fun h => (divEnd_lower h).2.2⟩
      · exact ⟨fun h => ⟨(divEnd_upper h).1, (divEnd_upper h).2.1⟩, fun h => (divEnd_upper h).2.2⟩

#print axioms divEnd_master

/-- The export `divCore`, called on intervals `a` and `b`, accepts exactly when both are accepted,
their endpoints are finite, the values of the endpoints of `b` are not zero, and every IEEE 754
quotient of an endpoint of `a` by an endpoint of `b` is finite and stays finite one step down and
one step up; the value of the result's lower endpoint is then the least of those quotients moved
one step down, the value of its upper endpoint the greatest of them moved one step up, and when the
values of the endpoints of `b` lie on one side of zero the result contains `x / y` for every `x` in
`a` and `y` in `b`. -/
theorem divCore_master :
    Verified.Master compiled.module compiled.tables "divCore" compiled.divCore.bound
      (fun _ => True)
      (fun (x : Interval × Interval) (r : Interval) =>
        let a := x.1
        let b := x.2
        let q := fun u v : Float => Wasm.IEEE64.div u.toBits v.toBits
        (r.status = 0 ↔ a.status = 0 ∧ b.status = 0 ∧ Finite a.lo.toBits ∧ Finite a.hi.toBits ∧
          Finite b.lo.toBits ∧ Finite b.hi.toBits ∧ value b.lo.toBits ≠ 0 ∧
          value b.hi.toBits ≠ 0 ∧ ∀ u ∈ [a.lo, a.hi], ∀ v ∈ [b.lo, b.hi],
            Finite (q u v) ∧ Finite (nextDown (q u v)) ∧ Finite (nextUp (q u v))) ∧
        (r.status = 0 → Finite r.lo.toBits ∧ Finite r.hi.toBits ∧
          value r.lo.toBits =
            min (min (value (nextDown (q a.lo b.lo))) (value (nextDown (q a.lo b.hi))))
              (min (value (nextDown (q a.hi b.lo))) (value (nextDown (q a.hi b.hi)))) ∧
          value r.hi.toBits =
            max (max (value (nextUp (q a.lo b.lo))) (value (nextUp (q a.lo b.hi))))
              (max (value (nextUp (q a.hi b.lo))) (value (nextUp (q a.hi b.hi))))) ∧
        (r.status = 0 → ∀ s t, Contains a s → Contains b t →
          (0 < value b.lo.toBits ∨ value b.hi.toBits < 0) → Contains r (s / t))) :=
  .of_trapFree (.ofA compiled.divCore.trapFree) nofun divCore_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ =>
      ⟨divCore_status x.1 x.2, divCore_values, fun h => (divCore_sound h).2.2⟩

#print axioms divCore_master

/-- The export `div`, called on intervals `a` and `b`, accepts exactly when the value of `b.lo`
lies above zero or the value of `b.hi` below zero and the conditions of `divCore` hold; the
result's endpoints are then those of `divCore`, and the result contains `x / y`, with `y` not zero,
for every `x` in `a` and `y` in `b`. -/
theorem div_master :
    Verified.Master compiled.module compiled.tables "div" compiled.div.bound (fun _ => True)
      (fun (x : Interval × Interval) (r : Interval) =>
        let a := x.1
        let b := x.2
        let q := fun u v : Float => Wasm.IEEE64.div u.toBits v.toBits
        (r.status = 0 ↔ (0 < value b.lo.toBits ∨ value b.hi.toBits < 0) ∧ a.status = 0 ∧
          b.status = 0 ∧ Finite a.lo.toBits ∧ Finite a.hi.toBits ∧ Finite b.lo.toBits ∧
          Finite b.hi.toBits ∧ value b.lo.toBits ≠ 0 ∧ value b.hi.toBits ≠ 0 ∧
          ∀ u ∈ [a.lo, a.hi], ∀ v ∈ [b.lo, b.hi],
            Finite (q u v) ∧ Finite (nextDown (q u v)) ∧ Finite (nextUp (q u v))) ∧
        (r.status = 0 → Finite r.lo.toBits ∧ Finite r.hi.toBits ∧
          value r.lo.toBits =
            min (min (value (nextDown (q a.lo b.lo))) (value (nextDown (q a.lo b.hi))))
              (min (value (nextDown (q a.hi b.lo))) (value (nextDown (q a.hi b.hi)))) ∧
          value r.hi.toBits =
            max (max (value (nextUp (q a.lo b.lo))) (value (nextUp (q a.lo b.hi))))
              (max (value (nextUp (q a.hi b.lo))) (value (nextUp (q a.hi b.hi))))) ∧
        (r.status = 0 → ∀ s t, Contains a s → Contains b t → t ≠ 0 ∧ Contains r (s / t))) :=
  .of_trapFree (.ofA compiled.div.trapFree) nofun div_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      refine ⟨by rw [div_status, divCore_status], fun h => ?_, fun h => (div_sound h).2.2⟩
      have hc : (divCore x.1 x.2).status = 0 := by rw [← div_eq_divCore h]; exact h
      rw [div_eq_divCore h]
      exact divCore_values hc

#print axioms div_master

/-- The export `sqrt`, called on an interval `a`, accepts exactly when `a` is accepted, its
endpoints are finite with values that are not negative, and the IEEE 754 square roots of its
endpoints are finite and stay finite one step outward; it then returns the root of the lower
endpoint one step down and the root of the upper endpoint one step up, an interval that contains
`√x` for every `x` in `a`. -/
theorem sqrt_master :
    Verified.Master compiled.module compiled.tables "sqrt" compiled.sqrt.bound (fun _ => True)
      (fun (a : Interval) (r : Interval) =>
        let l := Wasm.IEEE64.sqrt a.lo.toBits
        let h := Wasm.IEEE64.sqrt a.hi.toBits
        (r.status = 0 ↔ a.status = 0 ∧ Finite a.lo.toBits ∧ 0 ≤ value a.lo.toBits ∧ Finite l ∧
          Finite (nextDown l) ∧ Finite a.hi.toBits ∧ 0 ≤ value a.hi.toBits ∧ Finite h ∧
          Finite (nextUp h)) ∧
        (r.status = 0 → r.lo.toBits = nextDown l ∧ r.hi.toBits = nextUp h) ∧
        (r.status = 0 → ∀ t, Contains a t → 0 ≤ t ∧ Contains r (Real.sqrt t))) :=
  .of_trapFree (.ofA compiled.sqrt.trapFree) nofun sqrt_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ a _ _ => by
      obtain ⟨hs, hv⟩ := join_endpoints (ok := a.status == 0)
        (outSqrt_outward false a.lo).lower.1 (outSqrt_outward true a.hi).upper.1
      simp only [beq_iff_eq, and_assoc] at hs
      exact ⟨hs, hv, fun h => (sqrt_sound h).2⟩

#print axioms sqrt_master

/-- The export `abs`, called on an interval `a`, accepts exactly when `a` is accepted, and then
returns `a` when `0 ≤ a.lo`, the interval from `-a.hi` to `-a.lo` when `a.hi ≤ 0`, and the
interval from `0` to Lean's `max` of `-a.lo` and `a.hi` otherwise, an interval that contains `|x|`
for every `x` in `a`. -/
theorem abs_master :
    Verified.Master compiled.module compiled.tables "abs" compiled.abs.bound (fun _ => True)
      (fun (a : Interval) (r : Interval) =>
        (r.status = 0 ↔ a.status = 0) ∧
        (r.status = 0 →
          if 0 ≤ a.lo then r.lo = a.lo ∧ r.hi = a.hi
          else if a.hi ≤ 0 then r.lo = -a.hi ∧ r.hi = -a.lo
          else r.lo = 0 ∧ r.hi = max (-a.lo) a.hi) ∧
        (r.status = 0 → ∀ t, Contains a t → Contains r |t|)) :=
  .of_trapFree (.ofA compiled.abs.trapFree) nofun abs_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ a _ _ => ⟨abs_status a, abs_fields, fun h => (abs_sound h).2⟩

#print axioms abs_master

/-- The export `clamp`, called on an interval `a` and floats `lo` and `hi`, accepts exactly when
`a` is accepted and `lo` and `hi` are finite, and then returns the interval from Lean's `max` of
`a.lo` and `lo` to Lean's `min` of `a.hi` and `hi`, which contains every `x` in `a` between the
values of `lo` and `hi`. -/
theorem clamp_master :
    Verified.Master compiled.module compiled.tables "clamp" compiled.clamp.bound (fun _ => True)
      (fun (x : Interval × Float × Float) (r : Interval) =>
        let a := x.1
        let lo := x.2.1
        let hi := x.2.2
        (r.status = 0 ↔ a.status = 0 ∧ Finite lo.toBits ∧ Finite hi.toBits) ∧
        (r.status = 0 → r.lo = max a.lo lo ∧ r.hi = min a.hi hi) ∧
        (r.status = 0 → ∀ t, Contains a t → value lo.toBits ≤ t → t ≤ value hi.toBits →
          Contains r t)) :=
  .of_trapFree (.ofA compiled.clamp.trapFree) nofun clamp_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ =>
      ⟨clamp_status x.1 x.2.1 x.2.2, clamp_fields, fun h => (clamp_sound h).2⟩

#print axioms clamp_master

/-- The export `outward2`, called on a direction `up` and a float `w`, accepts exactly when `w`
and the words one and two steps from it, up for `up` and down otherwise, are finite, and then
returns the word two steps away, which lies at or above every real `t` for `up`, and at or below
it otherwise, when `w` is within one step of the nearest-even rounding of `t`. -/
theorem outward2_master :
    Verified.Master compiled.module compiled.tables "outward2" compiled.outward2.bound
      (fun _ => True)
      (fun (x : Bool × Float) (c : Checked) =>
        let up := x.1
        let w := x.2.toBits
        (c.status = 0 ↔ Finite w ∧ Finite (F64Outward.neighbor up w) ∧
          Finite (F64Outward.neighbor up (F64Outward.neighbor up w))) ∧
        (c.status = 0 → c.value.toBits = F64Outward.neighbor up (F64Outward.neighbor up w)) ∧
        (c.status = 0 → ∀ t, F64SignedRounding.WithinSteps 1 t w →
          if up then t ≤ value c.value.toBits else value c.value.toBits ≤ t)) :=
  .of_trapFree (.ofA compiled.outward2.trapFree) nofun outward2_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ =>
      ⟨(outward2_spec x.1 x.2).1, (outward2_spec x.1 x.2).2, fun h _ ht => outward2_meaning h ht⟩

#print axioms outward2_master

/-- The export `increasing`, called on an interval `a` and floats `flo` and `fhi`, accepts exactly
when `a` is accepted and `flo` and the words one and two steps below it, and `fhi` and the words
one and two steps above it, are finite; it then returns the interval from two steps below `flo` to
two steps above `fhi`, which contains `f x` for every `x` in `a` and every `f` increasing on the
values of `a` with `flo` and `fhi` within one step of the nearest-even rounding of `f` at the
values of the finite endpoints. -/
theorem increasing_master :
    Verified.Master compiled.module compiled.tables "increasing" compiled.increasing.bound
      (fun _ => True)
      (fun (x : Interval × Float × Float) (r : Interval) =>
        let a := x.1
        let flo := x.2.1.toBits
        let fhi := x.2.2.toBits
        (r.status = 0 ↔ a.status = 0 ∧ Finite flo ∧ Finite (nextDown flo) ∧
          Finite (nextDown (nextDown flo)) ∧ Finite fhi ∧ Finite (nextUp fhi) ∧
          Finite (nextUp (nextUp fhi))) ∧
        (r.status = 0 → r.lo.toBits = nextDown (nextDown flo) ∧ r.hi.toBits = nextUp (nextUp fhi)) ∧
        (r.status = 0 → ∀ f : ℝ → ℝ,
          MonotoneOn f (Set.Icc (value a.lo.toBits) (value a.hi.toBits)) →
          (Finite a.lo.toBits → F64SignedRounding.WithinSteps 1 (f (value a.lo.toBits)) flo) →
          (Finite a.hi.toBits → F64SignedRounding.WithinSteps 1 (f (value a.hi.toBits)) fhi) →
          ∀ t, Contains a t → Contains r (f t))) :=
  .of_trapFree (.ofA compiled.increasing.trapFree) nofun increasing_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      obtain ⟨hs, hv⟩ := join_endpoints (ok := x.1.status == 0) (outward2_down x.2.1)
        (outward2_up x.2.2)
      simp only [beq_iff_eq, and_assoc] at hs
      exact ⟨hs, hv, fun h _ hf hlo hhi => (increasing_sound h hf hlo hhi).2⟩

#print axioms increasing_master

/-- The export `decreasing`, called on an interval `a` and floats `flo` and `fhi`, accepts exactly
when `a` is accepted and `fhi` and the words one and two steps below it, and `flo` and the words
one and two steps above it, are finite; it then returns the interval from two steps below `fhi` to
two steps above `flo`, which contains `f x` for every `x` in `a` and every `f` decreasing on the
values of `a` with `flo` and `fhi` within one step of the nearest-even rounding of `f` at the
values of the finite endpoints. -/
theorem decreasing_master :
    Verified.Master compiled.module compiled.tables "decreasing" compiled.decreasing.bound
      (fun _ => True)
      (fun (x : Interval × Float × Float) (r : Interval) =>
        let a := x.1
        let flo := x.2.1.toBits
        let fhi := x.2.2.toBits
        (r.status = 0 ↔ a.status = 0 ∧ Finite fhi ∧ Finite (nextDown fhi) ∧
          Finite (nextDown (nextDown fhi)) ∧ Finite flo ∧ Finite (nextUp flo) ∧
          Finite (nextUp (nextUp flo))) ∧
        (r.status = 0 → r.lo.toBits = nextDown (nextDown fhi) ∧ r.hi.toBits = nextUp (nextUp flo)) ∧
        (r.status = 0 → ∀ f : ℝ → ℝ,
          AntitoneOn f (Set.Icc (value a.lo.toBits) (value a.hi.toBits)) →
          (Finite a.lo.toBits → F64SignedRounding.WithinSteps 1 (f (value a.lo.toBits)) flo) →
          (Finite a.hi.toBits → F64SignedRounding.WithinSteps 1 (f (value a.hi.toBits)) fhi) →
          ∀ t, Contains a t → Contains r (f t))) :=
  .of_trapFree (.ofA compiled.decreasing.trapFree) nofun decreasing_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      obtain ⟨hs, hv⟩ := join_endpoints (ok := x.1.status == 0) (outward2_down x.2.2)
        (outward2_up x.2.1)
      simp only [beq_iff_eq, and_assoc] at hs
      exact ⟨hs, hv, fun h _ hf hlo hhi => (decreasing_sound h hf hlo hhi).2⟩

#print axioms decreasing_master

end Library.Numerics.Interval
