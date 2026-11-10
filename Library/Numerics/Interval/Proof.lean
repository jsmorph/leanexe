import Library.Numerics.Interval.Program
import Library.Numerics.Bounds.Proof
import LeanExe.ProofKit.F64Magnitude
import LeanExe.ProofKit.F64Sign
import Library.Numerics.Interval.Steps

/-!
Soundness of the interval operations.  `Contains i x` states that the interval `i` is accepted,
that its endpoints are finite, and that the real `x` lies between their values.  Each theorem
takes an accepted result and gives the acceptance of the operands and the inclusion of the real
result for every real point of the operands.
-/

namespace Library.Numerics.Interval

open LeanExe.ProofKit Library.Numerics.Bounds
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

def Contains (i : Interval) (x : ℝ) : Prop :=
  i.status = 0 ∧ Finite i.lo.toBits ∧ Finite i.hi.toBits ∧
    value i.lo.toBits ≤ x ∧ x ≤ value i.hi.toBits

/-! ### Floats -/

theorem finite_iff (x : Float) : finite x = true ↔ Finite x.toBits := by
  rw [← F64Order.finiteBits_iff]
  simp only [finite, absBits, F64Order.finiteBits, F64Order.absBits]
  exact ⟨fun h => decide_eq_true (of_decide_eq_true h), fun h => decide_eq_true (of_decide_eq_true h)⟩

theorem le_iff_value {a b : Float} (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a ≤ b ↔ value a.toBits ≤ value b.toBits := by
  rw [F64Bits.le_iff]
  simp only [Wasm.IEEE64.le, CodeLib.IEEE64.not_nan_of_finite ha,
    CodeLib.IEEE64.not_nan_of_finite hb, Bool.or_false, Bool.false_eq_true, ite_false,
    decide_eq_true_eq, value]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

theorem lt_iff_value {a b : Float} (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a < b ↔ value a.toBits < value b.toBits := by
  rw [F64Bits.lt_iff]
  simp only [Wasm.IEEE64.lt, CodeLib.IEEE64.not_nan_of_finite ha,
    CodeLib.IEEE64.not_nan_of_finite hb, Bool.or_false, Bool.false_eq_true, ite_false,
    decide_eq_true_eq, value]
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

theorem zero_value : Finite (0 : Float).toBits ∧ value (0 : Float).toBits = 0 := by
  have hs : Wasm.IEEE64.scaledValue 0 = 0 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [zero_toBits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [zero_toBits, value, hs]; norm_num

theorem neg_value {x : Float} (hx : Finite x.toBits) :
    Finite (-x).toBits ∧ value (-x).toBits = -value x.toBits := by
  have hn : Wasm.IEEE64.isNaN x.toBits = false := CodeLib.IEEE64.not_nan_of_finite hx
  have e : (-x).toBits = Wasm.IEEE64.negate x.toBits := by
    simp only [F64Bits.toBits_neg, F64Sign.sub_negZero, hn, Bool.false_eq_true, ite_false]
  rw [e]
  exact F64Magnitude.negate_value _ hx

theorem fmin_value {a b : Float} (ha : Finite a.toBits) (hb : Finite b.toBits) :
    Finite (fmin a b).toBits ∧ value (fmin a b).toBits = min (value a.toBits) (value b.toBits) := by
  unfold fmin
  by_cases h : a ≤ b
  · simp only [h, ite_true]
    exact ⟨ha, (min_eq_left ((le_iff_value ha hb).mp h)).symm⟩
  · simp only [h, ite_false]
    have hv : value b.toBits ≤ value a.toBits :=
      le_of_lt (not_le.mp fun h' => h ((le_iff_value ha hb).mpr h'))
    exact ⟨hb, (min_eq_right hv).symm⟩

theorem fmax_value {a b : Float} (ha : Finite a.toBits) (hb : Finite b.toBits) :
    Finite (fmax a b).toBits ∧ value (fmax a b).toBits = max (value a.toBits) (value b.toBits) := by
  unfold fmax
  by_cases h : a ≤ b
  · simp only [h, ite_true]
    exact ⟨hb, (max_eq_right ((le_iff_value ha hb).mp h)).symm⟩
  · simp only [h, ite_false]
    have hv : value b.toBits ≤ value a.toBits :=
      le_of_lt (not_le.mp fun h' => h ((le_iff_value ha hb).mpr h'))
    exact ⟨ha, (max_eq_left hv).symm⟩

/-! ### Checked endpoints -/

theorem lower {c : Checked} {x : ℝ} (h : F64Outward.Sound false (checkedWord c) x) :
    Finite c.value.toBits ∧ value c.value.toBits ≤ x :=
  F64Outward.sound_lower h

theorem upper {c : Checked} {x : ℝ} (h : F64Outward.Sound true (checkedWord c) x) :
    Finite c.value.toBits ∧ x ≤ value c.value.toBits :=
  F64Outward.sound_upper h

theorem join_accepted {ok : Bool} {l h : Checked} (hs : (join ok l h).status = 0) :
    ok = true ∧ l.status = 0 ∧ h.status = 0 ∧ join ok l h = ⟨0, l.value, h.value⟩ := by
  unfold join at hs ⊢
  by_cases hc : (ok && l.status == 0 && h.status == 0) = true
  · simp only [hc, ite_true]
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, trivial⟩
  · simp only [hc, Bool.false_eq_true, ite_false] at hs
    exact absurd hs (by decide)

theorem extreme_accepted {up : Bool} {p q r s : Checked}
    (h : (extreme up p q r s).status = 0) :
    p.status = 0 ∧ q.status = 0 ∧ r.status = 0 ∧ s.status = 0 := by
  unfold extreme at h
  by_cases hc : (p.status == 0 && q.status == 0 && r.status == 0 && s.status == 0) = true
  · simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
  · simp only [hc, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem extreme_lower {p q r s : Checked} (h : (extreme false p q r s).status = 0)
    (fp : Finite p.value.toBits) (fq : Finite q.value.toBits) (fr : Finite r.value.toBits)
    (fs : Finite s.value.toBits) :
    Finite (extreme false p q r s).value.toBits ∧
      value (extreme false p q r s).value.toBits =
        min (min (value p.value.toBits) (value q.value.toBits))
          (min (value r.value.toBits) (value s.value.toBits)) := by
  obtain ⟨h1, h2, h3, h4⟩ := extreme_accepted h
  obtain ⟨f1, v1⟩ := fmin_value fp fq
  obtain ⟨f2, v2⟩ := fmin_value fr fs
  obtain ⟨f3, v3⟩ := fmin_value f1 f2
  simp only [extreme, h1, h2, h3, h4, beq_self_eq_true, Bool.and_self, ite_true,
    Bool.false_eq_true, ite_false]
  exact ⟨f3, by rw [v3, v1, v2]⟩

theorem extreme_upper {p q r s : Checked} (h : (extreme true p q r s).status = 0)
    (fp : Finite p.value.toBits) (fq : Finite q.value.toBits) (fr : Finite r.value.toBits)
    (fs : Finite s.value.toBits) :
    Finite (extreme true p q r s).value.toBits ∧
      value (extreme true p q r s).value.toBits =
        max (max (value p.value.toBits) (value q.value.toBits))
          (max (value r.value.toBits) (value s.value.toBits)) := by
  obtain ⟨h1, h2, h3, h4⟩ := extreme_accepted h
  obtain ⟨f1, v1⟩ := fmax_value fp fq
  obtain ⟨f2, v2⟩ := fmax_value fr fs
  obtain ⟨f3, v3⟩ := fmax_value f1 f2
  simp only [extreme, h1, h2, h3, h4, beq_self_eq_true, Bool.and_self, ite_true]
  exact ⟨f3, by rw [v3, v1, v2]⟩

/-! ### Real bounds of products and quotients -/

theorem le_mul_of_corners {l a1 a2 b1 b2 x y : ℝ} (hx1 : a1 ≤ x) (hx2 : x ≤ a2)
    (hy1 : b1 ≤ y) (hy2 : y ≤ b2) (h11 : l ≤ a1 * b1) (h12 : l ≤ a1 * b2)
    (h21 : l ≤ a2 * b1) (h22 : l ≤ a2 * b2) : l ≤ x * y := by
  have side : ∀ b, l ≤ a1 * b → l ≤ a2 * b → l ≤ x * b := by
    intro b h1 h2
    rcases le_total 0 b with hb | hb
    · exact h1.trans (mul_le_mul_of_nonneg_right hx1 hb)
    · exact h2.trans (mul_le_mul_of_nonpos_right hx2 hb)
  rcases le_total 0 x with h | h
  · exact (side b1 h11 h21).trans (mul_le_mul_of_nonneg_left hy1 h)
  · exact (side b2 h12 h22).trans (mul_le_mul_of_nonpos_left hy2 h)

theorem mul_le_of_corners {u a1 a2 b1 b2 x y : ℝ} (hx1 : a1 ≤ x) (hx2 : x ≤ a2)
    (hy1 : b1 ≤ y) (hy2 : y ≤ b2) (h11 : a1 * b1 ≤ u) (h12 : a1 * b2 ≤ u)
    (h21 : a2 * b1 ≤ u) (h22 : a2 * b2 ≤ u) : x * y ≤ u := by
  have side : ∀ b, a1 * b ≤ u → a2 * b ≤ u → x * b ≤ u := by
    intro b h1 h2
    rcases le_total 0 b with hb | hb
    · exact (mul_le_mul_of_nonneg_right hx2 hb).trans h2
    · exact (mul_le_mul_of_nonpos_right hx1 hb).trans h1
  rcases le_total 0 x with h | h
  · exact (mul_le_mul_of_nonneg_left hy2 h).trans (side b2 h12 h22)
  · exact (mul_le_mul_of_nonpos_left hy1 h).trans (side b1 h11 h21)

/-- The reciprocal of a point of an interval that excludes zero lies between the reciprocals of
the ends. -/
theorem inv_between {b1 b2 y : ℝ} (hy1 : b1 ≤ y) (hy2 : y ≤ b2) (hz : 0 < b1 ∨ b2 < 0) :
    b2⁻¹ ≤ y⁻¹ ∧ y⁻¹ ≤ b1⁻¹ := by
  rcases hz with hz | hz
  · have hy : 0 < y := lt_of_lt_of_le hz hy1
    exact ⟨inv_anti₀ hy hy2, inv_anti₀ hz hy1⟩
  · have hy : y < 0 := lt_of_le_of_lt hy2 hz
    have hb : b1 < 0 := lt_of_le_of_lt hy1 hy
    exact ⟨(inv_le_inv_of_neg hz hy).mpr hy2, (inv_le_inv_of_neg hy hb).mpr hy1⟩

theorem le_div_of_corners {l a1 a2 b1 b2 x y : ℝ} (hx1 : a1 ≤ x) (hx2 : x ≤ a2)
    (hy1 : b1 ≤ y) (hy2 : y ≤ b2) (hz : 0 < b1 ∨ b2 < 0) (h11 : l ≤ a1 / b1)
    (h12 : l ≤ a1 / b2) (h21 : l ≤ a2 / b1) (h22 : l ≤ a2 / b2) : l ≤ x / y := by
  obtain ⟨i1, i2⟩ := inv_between hy1 hy2 hz
  rw [div_eq_mul_inv] at h11 h12 h21 h22 ⊢
  exact le_mul_of_corners hx1 hx2 i1 i2 h12 h11 h22 h21

theorem div_le_of_corners {u a1 a2 b1 b2 x y : ℝ} (hx1 : a1 ≤ x) (hx2 : x ≤ a2)
    (hy1 : b1 ≤ y) (hy2 : y ≤ b2) (hz : 0 < b1 ∨ b2 < 0) (h11 : a1 / b1 ≤ u)
    (h12 : a1 / b2 ≤ u) (h21 : a2 / b1 ≤ u) (h22 : a2 / b2 ≤ u) : x / y ≤ u := by
  obtain ⟨i1, i2⟩ := inv_between hy1 hy2 hz
  rw [div_eq_mul_inv] at h11 h12 h21 h22 ⊢
  exact mul_le_of_corners hx1 hx2 i1 i2 h12 h11 h22 h21

/-! ### Construction -/

theorem make_sound {lo hi : Float} (h : (make lo hi).status = 0) :
    Finite lo.toBits ∧ Finite hi.toBits ∧ value lo.toBits ≤ value hi.toBits ∧
      ∀ x, value lo.toBits ≤ x → x ≤ value hi.toBits → Contains (make lo hi) x := by
  unfold make at h ⊢
  by_cases hf : (finite lo && finite hi) = true
  · by_cases hle : lo ≤ hi
    · simp only [hf, hle, ite_true]
      simp only [Bool.and_eq_true, finite_iff] at hf
      exact ⟨hf.1, hf.2, (le_iff_value hf.1 hf.2).mp hle,
        fun x h1 h2 => ⟨rfl, hf.1, hf.2, h1, h2⟩⟩
    · simp only [hf, hle, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [hf, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem point_sound {x : Float} (h : (point x).status = 0) :
    Finite x.toBits ∧ Contains (point x) (value x.toBits) := by
  unfold point at h ⊢
  by_cases hf : finite x = true
  · simp only [hf, ite_true]
    have hx := (finite_iff x).mp hf
    exact ⟨hx, rfl, hx, hx, le_rfl, le_rfl⟩
  · simp only [hf, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-! ### Arithmetic -/

theorem add_sound {a b : Interval} (h : (add a b).status = 0) :
    a.status = 0 ∧ b.status = 0 ∧
      ∀ x y, Contains a x → Contains b y → Contains (add a b) (x + y) := by
  unfold add at h ⊢
  obtain ⟨hok, hl, hh, he⟩ := join_accepted h
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨-, -, sl⟩ := outAdd_accepted hl
  obtain ⟨-, -, sh⟩ := outAdd_accepted hh
  obtain ⟨fl, bl⟩ := lower sl
  obtain ⟨fh, bh⟩ := upper sh
  refine ⟨hok.1, hok.2, fun x y hx hy => ?_⟩
  rw [he]
  exact ⟨rfl, fl, fh, by linarith [hx.2.2.2.1, hy.2.2.2.1], by linarith [hx.2.2.2.2, hy.2.2.2.2]⟩

theorem sub_sound {a b : Interval} (h : (sub a b).status = 0) :
    a.status = 0 ∧ b.status = 0 ∧
      ∀ x y, Contains a x → Contains b y → Contains (sub a b) (x - y) := by
  unfold sub at h ⊢
  obtain ⟨hok, hl, hh, he⟩ := join_accepted h
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨-, -, sl⟩ := outSub_accepted hl
  obtain ⟨-, -, sh⟩ := outSub_accepted hh
  obtain ⟨fl, bl⟩ := lower sl
  obtain ⟨fh, bh⟩ := upper sh
  refine ⟨hok.1, hok.2, fun x y hx hy => ?_⟩
  rw [he]
  exact ⟨rfl, fl, fh, by linarith [hx.2.2.2.1, hy.2.2.2.2], by linarith [hx.2.2.2.2, hy.2.2.2.1]⟩

theorem neg_sound {a : Interval} (h : (neg a).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (neg a) (-x) := by
  unfold neg at h ⊢
  by_cases hs : (a.status == 0) = true
  · simp only [hs, ite_true]
    refine ⟨beq_iff_eq.mp hs, fun x hx => ?_⟩
    obtain ⟨f1, v1⟩ := neg_value hx.2.2.1
    obtain ⟨f2, v2⟩ := neg_value hx.2.1
    exact ⟨rfl, f1, f2, by rw [v1]; linarith [hx.2.2.2.2], by rw [v2]; linarith [hx.2.2.2.1]⟩
  · simp only [hs, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem mul_sound {a b : Interval} (h : (mul a b).status = 0) :
    a.status = 0 ∧ b.status = 0 ∧
      ∀ x y, Contains a x → Contains b y → Contains (mul a b) (x * y) := by
  unfold mul at h ⊢
  obtain ⟨hok, hl, hh, he⟩ := join_accepted h
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  unfold mulEnd at hl hh he ⊢
  obtain ⟨l1, l2, l3, l4⟩ := extreme_accepted hl
  obtain ⟨u1, u2, u3, u4⟩ := extreme_accepted hh
  obtain ⟨fl1, bl1⟩ := lower (outMul_accepted l1).2.2
  obtain ⟨fl2, bl2⟩ := lower (outMul_accepted l2).2.2
  obtain ⟨fl3, bl3⟩ := lower (outMul_accepted l3).2.2
  obtain ⟨fl4, bl4⟩ := lower (outMul_accepted l4).2.2
  obtain ⟨fu1, bu1⟩ := upper (outMul_accepted u1).2.2
  obtain ⟨fu2, bu2⟩ := upper (outMul_accepted u2).2.2
  obtain ⟨fu3, bu3⟩ := upper (outMul_accepted u3).2.2
  obtain ⟨fu4, bu4⟩ := upper (outMul_accepted u4).2.2
  obtain ⟨fL, vL⟩ := extreme_lower hl fl1 fl2 fl3 fl4
  obtain ⟨fU, vU⟩ := extreme_upper hh fu1 fu2 fu3 fu4
  refine ⟨hok.1, hok.2, fun x y hx hy => ?_⟩
  obtain ⟨-, -, -, hx1, hx2⟩ := hx
  obtain ⟨-, -, -, hy1, hy2⟩ := hy
  rw [he]
  refine ⟨rfl, fL, fU, ?_, ?_⟩
  · rw [vL]
    exact le_mul_of_corners hx1 hx2 hy1 hy2
      (((min_le_left _ _).trans (min_le_left _ _)).trans bl1)
      (((min_le_left _ _).trans (min_le_right _ _)).trans bl2)
      (((min_le_right _ _).trans (min_le_left _ _)).trans bl3)
      (((min_le_right _ _).trans (min_le_right _ _)).trans bl4)
  · rw [vU]
    exact mul_le_of_corners hx1 hx2 hy1 hy2
      (bu1.trans ((le_max_left _ _).trans (le_max_left _ _)))
      (bu2.trans ((le_max_right _ _).trans (le_max_left _ _)))
      (bu3.trans ((le_max_left _ _).trans (le_max_right _ _)))
      (bu4.trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem divCore_sound {a b : Interval} (h : (divCore a b).status = 0) :
    a.status = 0 ∧ b.status = 0 ∧
      ∀ x y, Contains a x → Contains b y →
        (0 < value b.lo.toBits ∨ value b.hi.toBits < 0) → Contains (divCore a b) (x / y) := by
  unfold divCore at h ⊢
  obtain ⟨hok, hl, hh, he⟩ := join_accepted h
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  unfold divEnd at hl hh he ⊢
  obtain ⟨l1, l2, l3, l4⟩ := extreme_accepted hl
  obtain ⟨u1, u2, u3, u4⟩ := extreme_accepted hh
  obtain ⟨fl1, bl1⟩ := lower (outDiv_accepted l1).2.2.2
  obtain ⟨fl2, bl2⟩ := lower (outDiv_accepted l2).2.2.2
  obtain ⟨fl3, bl3⟩ := lower (outDiv_accepted l3).2.2.2
  obtain ⟨fl4, bl4⟩ := lower (outDiv_accepted l4).2.2.2
  obtain ⟨fu1, bu1⟩ := upper (outDiv_accepted u1).2.2.2
  obtain ⟨fu2, bu2⟩ := upper (outDiv_accepted u2).2.2.2
  obtain ⟨fu3, bu3⟩ := upper (outDiv_accepted u3).2.2.2
  obtain ⟨fu4, bu4⟩ := upper (outDiv_accepted u4).2.2.2
  obtain ⟨fL, vL⟩ := extreme_lower hl fl1 fl2 fl3 fl4
  obtain ⟨fU, vU⟩ := extreme_upper hh fu1 fu2 fu3 fu4
  refine ⟨hok.1, hok.2, fun x y hx hy hz => ?_⟩
  obtain ⟨-, -, -, hx1, hx2⟩ := hx
  obtain ⟨-, -, -, hy1, hy2⟩ := hy
  rw [he]
  refine ⟨rfl, fL, fU, ?_, ?_⟩
  · rw [vL]
    exact le_div_of_corners hx1 hx2 hy1 hy2 hz
      (((min_le_left _ _).trans (min_le_left _ _)).trans bl1)
      (((min_le_left _ _).trans (min_le_right _ _)).trans bl2)
      (((min_le_right _ _).trans (min_le_left _ _)).trans bl3)
      (((min_le_right _ _).trans (min_le_right _ _)).trans bl4)
  · rw [vU]
    exact div_le_of_corners hx1 hx2 hy1 hy2 hz
      (bu1.trans ((le_max_left _ _).trans (le_max_left _ _)))
      (bu2.trans ((le_max_right _ _).trans (le_max_left _ _)))
      (bu3.trans ((le_max_left _ _).trans (le_max_right _ _)))
      (bu4.trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem div_sound {a b : Interval} (h : (div a b).status = 0) :
    a.status = 0 ∧ b.status = 0 ∧
      ∀ x y, Contains a x → Contains b y → y ≠ 0 ∧ Contains (div a b) (x / y) := by
  unfold div at h ⊢
  by_cases h1 : 0 < b.lo
  · simp only [h1, ite_true] at h ⊢
    obtain ⟨sa, sb, hc⟩ := divCore_sound h
    refine ⟨sa, sb, fun x y hx hy => ?_⟩
    have hp : 0 < value b.lo.toBits := by
      have := (lt_iff_value zero_value.1 hy.2.1).mp h1
      rwa [zero_value.2] at this
    exact ⟨ne_of_gt (lt_of_lt_of_le hp hy.2.2.2.1), hc x y hx hy (Or.inl hp)⟩
  · by_cases h2 : b.hi < 0
    · simp only [h1, h2, ite_true, ite_false] at h ⊢
      obtain ⟨sa, sb, hc⟩ := divCore_sound h
      refine ⟨sa, sb, fun x y hx hy => ?_⟩
      have hn : value b.hi.toBits < 0 := by
        have := (lt_iff_value hy.2.2.1 zero_value.1).mp h2
        rwa [zero_value.2] at this
      exact ⟨ne_of_lt (lt_of_le_of_lt hy.2.2.2.2 hn), hc x y hx hy (Or.inr hn)⟩
    · simp only [h1, h2, ite_false] at h
      exact absurd h (by decide)

theorem sqrt_sound {a : Interval} (h : (sqrt a).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x → 0 ≤ x ∧ Contains (sqrt a) (Real.sqrt x) := by
  unfold sqrt at h ⊢
  obtain ⟨hok, hl, hh, he⟩ := join_accepted h
  obtain ⟨-, n1, sl⟩ := outSqrt_accepted hl
  obtain ⟨-, -, sh⟩ := outSqrt_accepted hh
  obtain ⟨fl, bl⟩ := lower sl
  obtain ⟨fh, bh⟩ := upper sh
  refine ⟨beq_iff_eq.mp hok, fun x hx => ?_⟩
  rw [he]
  exact ⟨n1.trans hx.2.2.2.1, rfl, fl, fh, bl.trans (Real.sqrt_le_sqrt hx.2.2.2.1),
    (Real.sqrt_le_sqrt hx.2.2.2.2).trans bh⟩

theorem abs_sound {a : Interval} (h : (abs a).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (abs a) |x| := by
  unfold abs at h ⊢
  by_cases hs : (a.status == 0) = true
  · simp only [hs, ite_true]
    refine ⟨beq_iff_eq.mp hs, fun x hx => ?_⟩
    obtain ⟨sa, fl, fh, hx1, hx2⟩ := hx
    obtain ⟨z0, zv⟩ := zero_value
    by_cases h1 : 0 ≤ a.lo
    · simp only [h1, ite_true]
      have hp : 0 ≤ value a.lo.toBits := by
        have := (le_iff_value z0 fl).mp h1
        rwa [zv] at this
      rw [abs_of_nonneg (hp.trans hx1)]
      exact ⟨sa, fl, fh, hx1, hx2⟩
    · have hp : value a.lo.toBits < 0 := by
        have := not_le.mp fun h' => h1 ((le_iff_value z0 fl).mpr h')
        rwa [zv] at this
      obtain ⟨f1, v1⟩ := neg_value fh
      obtain ⟨f2, v2⟩ := neg_value fl
      by_cases h2 : a.hi ≤ 0
      · simp only [h1, h2, ite_true, ite_false]
        have hn : value a.hi.toBits ≤ 0 := by
          have := (le_iff_value fh z0).mp h2
          rwa [zv] at this
        rw [abs_of_nonpos (hx2.trans hn)]
        exact ⟨rfl, f1, f2, by rw [v1]; linarith, by rw [v2]; linarith⟩
      · simp only [h1, h2, ite_false]
        obtain ⟨f3, v3⟩ := fmax_value f2 fh
        refine ⟨rfl, z0, f3, by rw [zv]; exact abs_nonneg x, ?_⟩
        rw [v3, v2]
        exact abs_le.mpr ⟨by linarith [le_max_left (-value a.lo.toBits) (value a.hi.toBits)],
          hx2.trans (le_max_right _ _)⟩
  · simp only [hs, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem clamp_sound {a : Interval} {lo hi : Float} (h : (clamp a lo hi).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x → value lo.toBits ≤ x → x ≤ value hi.toBits →
      Contains (clamp a lo hi) x := by
  unfold clamp at h ⊢
  by_cases hc : (a.status == 0 && finite lo && finite hi) = true
  · simp only [hc, ite_true]
    simp only [Bool.and_eq_true, beq_iff_eq, finite_iff] at hc
    refine ⟨hc.1.1, fun x hx h1 h2 => ?_⟩
    obtain ⟨f1, v1⟩ := fmax_value hx.2.1 hc.1.2
    obtain ⟨f2, v2⟩ := fmin_value hx.2.2.1 hc.2
    exact ⟨rfl, f1, f2, by rw [v1]; exact max_le hx.2.2.2.1 h1,
      by rw [v2]; exact le_min hx.2.2.2.2 h2⟩
  · simp only [hc, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-! ### Function enclosures -/

theorem endpoint_accepted {up : Bool} {b : UInt64} (h : (F64Outward.endpoint up b).status = 0) :
    Finite b ∧ Finite (F64Outward.neighbor up b) ∧
      (F64Outward.endpoint up b).value = F64Outward.neighbor up b := by
  by_cases hf : F64Order.finiteBits b = true
  · by_cases hn : F64Order.finiteBits (F64Outward.neighbor up b) = true
    · refine ⟨(F64Order.finiteBits_iff _).mp hf, (F64Order.finiteBits_iff _).mp hn, ?_⟩
      simp only [F64Outward.endpoint, hf, hn, ite_true]
    · simp only [F64Outward.endpoint, hf, hn, ite_true, Bool.false_eq_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [F64Outward.endpoint, hf, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

theorem endpoint_bits {up : Bool} {r : Float} (h : (endpoint up r).status = 0) :
    Finite r.toBits ∧ Finite (F64Outward.neighbor up r.toBits) ∧
      (endpoint up r).value.toBits = F64Outward.neighbor up r.toBits := by
  have e := endpoint_word up r
  have hs : (F64Outward.endpoint up r.toBits).status = 0 := by
    rw [← e]
    exact h
  obtain ⟨f1, f2, hv⟩ := endpoint_accepted hs
  rw [← e] at hv
  exact ⟨f1, f2, hv⟩

theorem outward2_bits {up : Bool} {w : Float} (h : (outward2 up w).status = 0) :
    Finite w.toBits ∧ Finite (F64Outward.neighbor up w.toBits) ∧
      Finite (F64Outward.neighbor up (F64Outward.neighbor up w.toBits)) ∧
      (outward2 up w).value.toBits =
        F64Outward.neighbor up (F64Outward.neighbor up w.toBits) := by
  unfold outward2 at h ⊢
  by_cases he : ((endpoint up w).status == 0) = true
  · simp only [he, ite_true] at h ⊢
    obtain ⟨f1, f2, hv⟩ := endpoint_bits (beq_iff_eq.mp he)
    obtain ⟨-, f3, hv2⟩ := endpoint_bits h
    rw [hv] at f3 hv2
    exact ⟨f1, f2, f3, hv2⟩
  · simp only [he, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-- Two steps above a word within one step of the reference of `y`. -/
theorem outward2_upper {w : Float} {y : ℝ} (hw : F64SignedRounding.WithinSteps 1 y w.toBits)
    (h : (outward2 true w).status = 0) :
    Finite (outward2 true w).value.toBits ∧ y ≤ value (outward2 true w).value.toBits := by
  obtain ⟨f1, f2, f3, hv⟩ := outward2_bits h
  rw [hv]
  exact ⟨f3, Steps.two_up y _ hw f1 f2 f3⟩

/-- Two steps below a word within one step of the reference of `y`. -/
theorem outward2_lower {w : Float} {y : ℝ} (hw : F64SignedRounding.WithinSteps 1 y w.toBits)
    (h : (outward2 false w).status = 0) :
    Finite (outward2 false w).value.toBits ∧ value (outward2 false w).value.toBits ≤ y := by
  obtain ⟨f1, f2, f3, hv⟩ := outward2_bits h
  rw [hv]
  exact ⟨f3, Steps.two_down y _ hw f1 f2 f3⟩

/-- The image of an interval under a function that is increasing on it, from computed values
within one step of the nearest-even rounding of the function at the two ends, when the ends are
finite. -/
theorem increasing_sound {a : Interval} {flo fhi : Float} {f : ℝ → ℝ}
    (h : (increasing a flo fhi).status = 0)
    (hf : MonotoneOn f (Set.Icc (value a.lo.toBits) (value a.hi.toBits)))
    (hlo : Finite a.lo.toBits →
      F64SignedRounding.WithinSteps 1 (f (value a.lo.toBits)) flo.toBits)
    (hhi : Finite a.hi.toBits →
      F64SignedRounding.WithinSteps 1 (f (value a.hi.toBits)) fhi.toBits) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (increasing a flo fhi) (f x) := by
  unfold increasing at h ⊢
  obtain ⟨hok, hl, hh, he⟩ := join_accepted h
  refine ⟨beq_iff_eq.mp hok, fun x hx => ?_⟩
  obtain ⟨-, f1, f2, hx1, hx2⟩ := hx
  obtain ⟨fl, bl⟩ := outward2_lower (hlo f1) hl
  obtain ⟨fh, bh⟩ := outward2_upper (hhi f2) hh
  have hle := hx1.trans hx2
  rw [he]
  exact ⟨rfl, fl, fh, bl.trans (hf ⟨le_rfl, hle⟩ ⟨hx1, hx2⟩ hx1),
    (hf ⟨hx1, hx2⟩ ⟨hle, le_rfl⟩ hx2).trans bh⟩

/-- The image of an interval under a function that is decreasing on it. -/
theorem decreasing_sound {a : Interval} {flo fhi : Float} {f : ℝ → ℝ}
    (h : (decreasing a flo fhi).status = 0)
    (hf : AntitoneOn f (Set.Icc (value a.lo.toBits) (value a.hi.toBits)))
    (hlo : Finite a.lo.toBits →
      F64SignedRounding.WithinSteps 1 (f (value a.lo.toBits)) flo.toBits)
    (hhi : Finite a.hi.toBits →
      F64SignedRounding.WithinSteps 1 (f (value a.hi.toBits)) fhi.toBits) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (decreasing a flo fhi) (f x) := by
  unfold decreasing at h ⊢
  obtain ⟨hok, hl, hh, he⟩ := join_accepted h
  refine ⟨beq_iff_eq.mp hok, fun x hx => ?_⟩
  obtain ⟨-, f1, f2, hx1, hx2⟩ := hx
  obtain ⟨fl, bl⟩ := outward2_lower (hhi f2) hl
  obtain ⟨fh, bh⟩ := outward2_upper (hlo f1) hh
  have hle := hx1.trans hx2
  rw [he]
  exact ⟨rfl, fl, fh, bl.trans (hf ⟨hx1, hx2⟩ ⟨hle, le_rfl⟩ hx2),
    (hf ⟨le_rfl, hle⟩ ⟨hx1, hx2⟩ hx1).trans bh⟩

#print axioms finite_iff
#print axioms le_iff_value
#print axioms lt_iff_value
#print axioms zero_value
#print axioms neg_value
#print axioms fmin_value
#print axioms fmax_value
#print axioms lower
#print axioms upper
#print axioms join_accepted
#print axioms extreme_accepted
#print axioms extreme_lower
#print axioms extreme_upper
#print axioms le_mul_of_corners
#print axioms mul_le_of_corners
#print axioms inv_between
#print axioms le_div_of_corners
#print axioms div_le_of_corners
#print axioms make_sound
#print axioms point_sound
#print axioms add_sound
#print axioms sub_sound
#print axioms neg_sound
#print axioms mul_sound
#print axioms divCore_sound
#print axioms div_sound
#print axioms sqrt_sound
#print axioms abs_sound
#print axioms clamp_sound
#print axioms endpoint_accepted
#print axioms endpoint_bits
#print axioms outward2_bits
#print axioms outward2_upper
#print axioms outward2_lower
#print axioms increasing_sound
#print axioms decreasing_sound

end Library.Numerics.Interval
