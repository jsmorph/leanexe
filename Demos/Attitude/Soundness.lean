import Demos.Attitude.Program
import Demos.Attitude.Box
import Library.Numerics.Interval.Proof
import Library.Numerics.Float64.Asin.AsinTheorem

/-!
Soundness of the TRIAD program.  `triad_sound` states that a result of status 0 or 2 encloses
TRIAD's matrix of the real values of the inputs, whose vectors and cross products are then not
zero, and `triad_bound` that for status 0 every matrix in the intervals lies within `err` of every
true attitude that the error bounds admit.  The proofs relate `Spec.triadOf` and `Spec.boundOf` to
the model's `triadMat` and `hval`, apply the enclosure theorems of `enclosure_def`, and combine
`triad_error` with the box term `vangle_near` by the triangle inequality for angles.
-/

namespace Demos.Attitude

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)
open Demos.Slew.Spec Demos.Slew.Arc Demos.Slew.Normalize Demos.Slew.Premise Demos.Slew.Safety
open Demos.Slew.Rounding Vec Real

set_option exponentiation.threshold 4096

/-- The real vector of three floats. -/
noncomputable def vec3 (x y z : Float) : Vec := ⟨val x, val y, val z⟩

/-- The real `x` lies between the values of the endpoints of `i`. -/
def In (i : Interval) (x : ℝ) : Prop := value i.lo.toBits ≤ x ∧ x ≤ value i.hi.toBits

/-- The intervals of an estimate contain the entries of `T`. -/
def Inside (e : Estimate) (T : Mat) : Prop :=
  Contains e.m11 T.m11 ∧ Contains e.m12 T.m12 ∧ Contains e.m13 T.m13 ∧
  Contains e.m21 T.m21 ∧ Contains e.m22 T.m22 ∧ Contains e.m23 T.m23 ∧
  Contains e.m31 T.m31 ∧ Contains e.m32 T.m32 ∧ Contains e.m33 T.m33

/-- The entries of `M` lie between the endpoints of the intervals of an estimate. -/
def InBox (e : Estimate) (M : Mat) : Prop :=
  In e.m11 M.m11 ∧ In e.m12 M.m12 ∧ In e.m13 M.m13 ∧ In e.m21 M.m21 ∧ In e.m22 M.m22 ∧
  In e.m23 M.m23 ∧ In e.m31 M.m31 ∧ In e.m32 M.m32 ∧ In e.m33 M.m33

/-! ### Literals and points -/

theorem lit_neg_one : Finite (-1.0 : Float).toBits ∧ value (-1.0 : Float).toBits = -1 := by
  have hb : (-1.0 : Float).toBits = 0xBFF0000000000000 := by decide +kernel
  exact ⟨by rw [hb]; unfold CodeLib.IEEE64.Finite; decide +kernel, unit_bounds.1⟩

theorem lit_pos_one : Finite (1.0 : Float).toBits ∧ value (1.0 : Float).toBits = 1 := by
  have hb : (1.0 : Float).toBits = 0x3FF0000000000000 := by decide +kernel
  exact ⟨by rw [hb]; unfold CodeLib.IEEE64.Finite; decide +kernel, unit_bounds.2⟩

theorem lit_zero : Finite (0.0 : Float).toBits ∧ value (0.0 : Float).toBits = 0 := by
  have hb : (0.0 : Float).toBits = 0 := by decide +kernel
  have hs : Wasm.IEEE64.scaledValue 0 = 0 := by decide +kernel
  refine ⟨by rw [hb]; unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
  simp only [hb, value, hs]; norm_num

theorem lit_three_halves : Finite (1.5 : Float).toBits ∧ value (1.5 : Float).toBits = 3 / 2 := by
  have hb : (1.5 : Float).toBits = 0x3FF8000000000000 := by decide +kernel
  have hs : Wasm.IEEE64.scaledValue 0x3FF8000000000000 = 3 * 2 ^ 1073 := by decide +kernel
  refine ⟨by rw [hb]; unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
  simp only [hb, value, hs]; push_cast; norm_num

theorem lit_quarter : Finite (0.25 : Float).toBits ∧ value (0.25 : Float).toBits = 1 / 4 := by
  have hb : (0.25 : Float).toBits = 0x3FD0000000000000 := by decide +kernel
  have hs : Wasm.IEEE64.scaledValue 0x3FD0000000000000 = 2 ^ 1072 := by decide +kernel
  refine ⟨by rw [hb]; unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
  simp only [hb, value, hs]; push_cast; norm_num

theorem encloses_point (x : Float) : Encloses (point x) (val x) := fun h => (point_sound h).2

theorem rejected_status : (rejected : Interval).status ≠ 0 := by decide

/-- `asinI` encloses the arcsine. -/
theorem encloses_asinI {a : Interval} {x : ℝ} (ha : Encloses a x) :
    Encloses (asinI a) (arcsin x) := by
  intro h
  unfold asinI at h ⊢
  by_cases g : (a.status == 0 && -1.0 ≤ a.lo && a.hi ≤ 1.0) = true
  · simp only [g, ite_true] at h ⊢
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at g
    obtain ⟨⟨gs, glo⟩, ghi⟩ := g
    have c := ha gs
    obtain ⟨_, fl, fh, hl, hh⟩ := c
    have hlo : -1 ≤ value a.lo.toBits := by
      have := (le_iff_value lit_neg_one.1 fl).mp glo
      rwa [lit_neg_one.2] at this
    have hhi : value a.hi.toBits ≤ 1 := by
      have := (le_iff_value fh lit_pos_one.1).mp ghi
      rwa [lit_pos_one.2] at this
    have r := increasing_sound h (f := arcsin) (Real.monotone_arcsin.monotoneOn _)
      (fun _ => Asin.AsinTheorem.asin_within_one a.lo fl (abs_le.mpr ⟨hlo, by linarith⟩))
      (fun _ => Asin.AsinTheorem.asin_within_one a.hi fh (abs_le.mpr ⟨by linarith, hhi⟩))
    exact r.2 x (ha gs)
  · simp only [g, ite_false, Bool.false_eq_true] at h
    exact absurd h rejected_status

/-! ### The model's quantities -/

theorem triadOf_eq (b1 b2 r1 r2 : Vec) :
    Spec.triadOf b1.x b1.y b1.z b2.x b2.y b2.z r1.x r1.y r1.z r2.x r2.y r2.z =
      (Vec.norm b1, Vec.norm (cross b1 b2), Vec.norm r1, Vec.norm (cross r1 r2),
        (triadMat b1 b2 r1 r2).m11, (triadMat b1 b2 r1 r2).m12, (triadMat b1 b2 r1 r2).m13,
        (triadMat b1 b2 r1 r2).m21, (triadMat b1 b2 r1 r2).m22, (triadMat b1 b2 r1 r2).m23,
        (triadMat b1 b2 r1 r2).m31, (triadMat b1 b2 r1 r2).m32, (triadMat b1 b2 r1 r2).m33) := by
  simp only [Spec.triadOf, Spec.frameOf, Spec.matrixOf, triadMat, Frame.mat, frame, unit, smul,
    cross, Vec.norm, dot, Prod.mk.injEq]
  refine ⟨trivial, trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem norm_cross_unit {a b : Vec} (ha : 0 < norm a) (hb : 0 < norm b) :
    norm (cross (unit a) (unit b)) = norm (cross a b) / (norm a * norm b) := by
  rw [cross_unit_unit, Demos.Slew.Arc.norm_smul, abs_of_pos (by positivity)]
  field_simp

theorem boundOf_eq (e1 e2 : ℝ) {p q : Vec} (hp : 0 < norm p) (hq : 0 < norm q) :
    Spec.boundOf e1 e2 p.x p.y p.z q.x q.y q.z =
      (sin (e1 + e2) / norm (cross (unit p) (unit q)),
        hval e1 e2 (norm (cross (unit p) (unit q)))) := by
  rw [norm_cross_unit hp hq]
  simp only [Spec.boundOf, hval, Vec.norm, dot, cross, pow_two]

/-! ### What the statuses imply -/

/-- The conditions of an estimate of status other than 1. -/
theorem finish_cases {inv half : Array UInt64} {e1 e2 r1x r1y r1z r2x r2y r2z : Float}
    {r : Interval × Interval × Interval × Interval × Interval × Interval × Interval × Interval ×
      Interval × Interval × Interval × Interval × Interval}
    (h : (finishWith inv half e1 e2 r1x r1y r1z r2x r2y r2z r).status ≠ 1) :
    (r.1.status = 0 ∧ r.2.1.status = 0 ∧ r.2.2.1.status = 0 ∧ r.2.2.2.1.status = 0 ∧
      r.2.2.2.2.1.status = 0 ∧ r.2.2.2.2.2.1.status = 0 ∧ r.2.2.2.2.2.2.1.status = 0 ∧
      r.2.2.2.2.2.2.2.1.status = 0 ∧ r.2.2.2.2.2.2.2.2.1.status = 0 ∧
      r.2.2.2.2.2.2.2.2.2.1.status = 0 ∧ r.2.2.2.2.2.2.2.2.2.2.1.status = 0 ∧
      r.2.2.2.2.2.2.2.2.2.2.2.1.status = 0 ∧ r.2.2.2.2.2.2.2.2.2.2.2.2.status = 0) ∧
    (0 < r.1.lo ∧ 0 < r.2.1.lo ∧ 0 < r.2.2.1.lo ∧ 0 < r.2.2.2.1.lo) ∧
    finishWith inv half e1 e2 r1x r1y r1z r2x r2y r2z r =
      ⟨(boundWith inv half e1 e2 r1x r1y r1z r2x r2y r2z r.2.2.2.2.1 r.2.2.2.2.2.1
          r.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.2.1
          r.2.2.2.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.2.2.2.2).1,
        r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2.1,
        r.2.2.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2.2.2.2.1,
        r.2.2.2.2.2.2.2.2.2.2.2.2,
        (boundWith inv half e1 e2 r1x r1y r1z r2x r2y r2z r.2.2.2.2.1 r.2.2.2.2.2.1
          r.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.2.1
          r.2.2.2.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.2.2.2.2).2⟩ := by
  simp only [finishWith] at h ⊢
  split_ifs at h ⊢ with g1 g2
  · simp only [Bool.and_eq_true, beq_iff_eq] at g1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at g2
    exact ⟨⟨g1.1.1.1.1.1.1.1.1.1.1.1.1, g1.1.1.1.1.1.1.1.1.1.1.1.2, g1.1.1.1.1.1.1.1.1.1.1.2,
      g1.1.1.1.1.1.1.1.1.1.2, g1.1.1.1.1.1.1.1.1.2, g1.1.1.1.1.1.1.1.2, g1.1.1.1.1.1.1.2,
      g1.1.1.1.1.1.2, g1.1.1.1.1.2, g1.1.1.1.2, g1.1.1.2, g1.1.2, g1.2⟩,
      ⟨g2.1.1.1, g2.1.1.2, g2.1.2, g2.2⟩, rfl⟩
  · exact absurd rfl h
  · exact absurd rfl h

/-- The conditions of a bound of status 0. -/
theorem boundWith_cases {inv half : Array UInt64} {e1 e2 r1x r1y r1z r2x r2y r2z : Float}
    {m11 m12 m13 m21 m22 m23 m31 m32 m33 : Interval}
    (h : (boundWith inv half e1 e2 r1x r1y r1z r2x r2y r2z m11 m12 m13 m21 m22 m23 m31 m32
      m33).1 = 0) :
    0 ≤ e1 ∧ 0 ≤ e2 ∧ (add (point e1) (point e2)).status = 0 ∧
    (bdOf inv half e1 e2 r1x r1y r1z r2x r2y r2z).1.status = 0 ∧
    (etaOf m11 m12 m13 m21 m22 m23 m31 m32 m33).status = 0 ∧
    (add (point e1) (point e2)).hi ≤ 1.5 ∧ (bdOf inv half e1 e2 r1x r1y r1z r2x r2y r2z).1.hi < 1.0 ∧
    (etaOf m11 m12 m13 m21 m22 m23 m31 m32 m33).hi ≤ 0.25 ∧
    (errOf (bdOf inv half e1 e2 r1x r1y r1z r2x r2y r2z).2
      (etaOf m11 m12 m13 m21 m22 m23 m31 m32 m33)).status = 0 ∧
    (boundWith inv half e1 e2 r1x r1y r1z r2x r2y r2z m11 m12 m13 m21 m22 m23 m31 m32 m33).2 =
      (errOf (bdOf inv half e1 e2 r1x r1y r1z r2x r2y r2z).2
        (etaOf m11 m12 m13 m21 m22 m23 m31 m32 m33)).hi := by
  unfold boundWith at h ⊢
  by_cases g1 : (0 ≤ e1 && 0 ≤ e2 && (add (point e1) (point e2)).status == 0 &&
      (bdOf inv half e1 e2 r1x r1y r1z r2x r2y r2z).1.status == 0 &&
      (etaOf m11 m12 m13 m21 m22 m23 m31 m32 m33).status == 0) = true
  · simp only [g1, ↓reduceIte] at h ⊢
    by_cases g2 : ((add (point e1) (point e2)).hi ≤ 1.5 &&
        (bdOf inv half e1 e2 r1x r1y r1z r2x r2y r2z).1.hi < 1.0 &&
        (etaOf m11 m12 m13 m21 m22 m23 m31 m32 m33).hi ≤ 0.25) = true
    · simp only [g2, ↓reduceIte] at h ⊢
      by_cases g3 : ((errOf (bdOf inv half e1 e2 r1x r1y r1z r2x r2y r2z).2
          (etaOf m11 m12 m13 m21 m22 m23 m31 m32 m33)).status == 0) = true
      · simp only [g3, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at g1 g2 g3
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact g1.1.1.1.1
        · exact g1.1.1.1.2
        · exact g1.1.1.2
        · exact g1.1.2
        · exact g1.2
        · exact g2.1.1
        · exact g2.1.2
        · exact g2.2
        · exact g3
        · dsimp only
      · simp only [g3, Bool.false_eq_true, ↓reduceIte] at h; exact absurd h (by decide)
    · simp only [g2, Bool.false_eq_true, ↓reduceIte] at h; exact absurd h (by decide)
  · simp only [g1, Bool.false_eq_true, ↓reduceIte] at h; exact absurd h (by decide)

/-- The interval of `η` encloses the root of the sum of the squared widths. -/
theorem encloses_etaOf (m11 m12 m13 m21 m22 m23 m31 m32 m33 : Interval) :
    Encloses (etaOf m11 m12 m13 m21 m22 m23 m31 m32 m33)
      √(Mat.sumSq ⟨val m11.hi - val m11.lo, val m12.hi - val m12.lo, val m13.hi - val m13.lo,
        val m21.hi - val m21.lo, val m22.hi - val m22.lo, val m23.hi - val m23.lo,
        val m31.hi - val m31.lo, val m32.hi - val m32.lo, val m33.hi - val m33.lo⟩) := by
  have w : ∀ a : Interval, Encloses (sq (widthI a)) ((val a.hi - val a.lo) * (val a.hi - val a.lo)) :=
    fun a => encloses_sq (encloses_sub (encloses_point a.hi) (encloses_point a.lo))
  have e := encloses_sqrt (encloses_add (encloses_add
    (encloses_add (encloses_add (w m11) (w m12)) (w m13))
    (encloses_add (encloses_add (w m21) (w m22)) (w m23)))
    (encloses_add (encloses_add (w m31) (w m32)) (w m33)))
  unfold etaOf
  convert e using 2
  simp only [Mat.sumSq]; ring

/-- Clamping to `[0, 1]` keeps the enclosure of a real in `[0, 1]`. -/
theorem encloses_clamp01 {a : Interval} {x : ℝ} (ha : Encloses a x) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Encloses (clamp a 0 1.0) x := by
  intro h
  obtain ⟨sa, hc⟩ := clamp_sound h
  exact hc x (ha sa) (by rw [zero_value.2]; exact h0) (by rw [lit_pos_one.2]; exact h1)

/-- The interval of the bound encloses `2 arcsin √h + arcsin (η / (1 - η))` for `h` in `[0, 1]`. -/
theorem encloses_errOf {h eta : Interval} {hv ηv : ℝ} (hh : Encloses h hv) (h0 : 0 ≤ hv)
    (h1 : hv ≤ 1) (he : Encloses eta ηv) :
    Encloses (errOf h eta) (2 * arcsin √hv + arcsin (ηv / (1 - ηv))) := by
  have two : Encloses (ofInt 2) (2 : ℝ) :=
    encloses_ofInt' (m := 2) (by decide +kernel) (by decide +kernel) (by norm_num)
  have one : Encloses (ofInt 1) (1 : ℝ) :=
    encloses_ofInt' (m := 1) (by decide +kernel) (by decide +kernel) (by norm_num)
  exact encloses_add (encloses_mul two (encloses_asinI (encloses_sqrt (encloses_clamp01 hh h0 h1))))
    (encloses_asinI (encloses_div he (encloses_sub one he)))

theorem norm_pos_right {a b : Vec} (h : 0 < norm (cross a b)) : 0 < norm b := by
  have h1 := norm_cross_le a b
  have h2 := Demos.Slew.Arc.norm_nonneg a
  have h3 := Demos.Slew.Arc.norm_nonneg b
  by_contra hb
  have : norm b = 0 := le_antisymm (not_lt.mp hb) h3
  rw [this, mul_zero] at h1
  linarith

theorem vec3_x (x y z : Float) : (vec3 x y z).x = val x := rfl
theorem vec3_y (x y z : Float) : (vec3 x y z).y = val y := rfl
theorem vec3_z (x y z : Float) : (vec3 x y z).z = val z := rfl

/-- The intervals of `Spec.triadOfI` on the inputs' points enclose the model's lengths and
matrix. -/
theorem triadOf_encloses (b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z : Float) :
    (enclosure_relation% 13)
      (Spec.triadOfI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point b1x) (point b1y)
        (point b1z) (point b2x) (point b2y) (point b2z) (point r1x) (point r1y) (point r1z)
        (point r2x) (point r2y) (point r2z))
      (norm (vec3 b1x b1y b1z), norm (cross (vec3 b1x b1y b1z) (vec3 b2x b2y b2z)),
        norm (vec3 r1x r1y r1z), norm (cross (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)),
        (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)).m11,
        (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)).m12,
        (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)).m13,
        (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)).m21,
        (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)).m22,
        (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)).m23,
        (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)).m31,
        (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)).m32,
        (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)).m33) := by
  have hr := Spec.triadOf.encloses (powLog := Trig.invPi) (powExp := Trig.invPi)
    (encloses_point b1x) (encloses_point b1y) (encloses_point b1z) (encloses_point b2x)
    (encloses_point b2y) (encloses_point b2z) (encloses_point r1x) (encloses_point r1y)
    (encloses_point r1z) (encloses_point r2x) (encloses_point r2y) (encloses_point r2z)
  have e := triadOf_eq (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)
  simp only [vec3_x, vec3_y, vec3_z] at e
  rwa [e] at hr

/-- **The enclosure of TRIAD's matrix.**  For a result of status 0 or 2, the vectors and the cross
products of the real values of the inputs are not zero, and the intervals contain the entries of
TRIAD's matrix. -/
theorem triad_sound {b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2 : Float}
    (h : (triad b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2).status ≠ 1) :
    0 < norm (vec3 b1x b1y b1z) ∧ 0 < norm (cross (vec3 b1x b1y b1z) (vec3 b2x b2y b2z)) ∧
    0 < norm (vec3 r1x r1y r1z) ∧ 0 < norm (cross (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)) ∧
    Inside (triad b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2)
      (triadMat (vec3 b1x b1y b1z) (vec3 b2x b2y b2z) (vec3 r1x r1y r1z) (vec3 r2x r2y r2z)) := by
  have hr := triadOf_encloses b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z
  simp only [triad, triadWith] at h ⊢
  generalize Spec.triadOfI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point b1x) (point b1y)
    (point b1z) (point b2x) (point b2y) (point b2z) (point r1x) (point r1y) (point r1z)
    (point r2x) (point r2y) (point r2z) = r at hr h ⊢
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13⟩, ⟨p1, p2, p3, p4⟩, he⟩ :=
    finish_cases h
  rw [he]
  exact ⟨(hr.1 s1).pos_of_lo p1, (hr.2.1 s2).pos_of_lo p2, (hr.2.2.1 s3).pos_of_lo p3,
    (hr.2.2.2.1 s4).pos_of_lo p4, hr.2.2.2.2.1 s5, hr.2.2.2.2.2.1 s6, hr.2.2.2.2.2.2.1 s7,
    hr.2.2.2.2.2.2.2.1 s8, hr.2.2.2.2.2.2.2.2.1 s9, hr.2.2.2.2.2.2.2.2.2.1 s10,
    hr.2.2.2.2.2.2.2.2.2.2.1 s11, hr.2.2.2.2.2.2.2.2.2.2.2.1 s12, hr.2.2.2.2.2.2.2.2.2.2.2.2 s13⟩

/-- The interval of `x` and `h` on the inputs' points encloses the model's quantities. -/
theorem bdOf_encloses (e1 e2 r1x r1y r1z r2x r2y r2z : Float)
    (hr1 : 0 < norm (vec3 r1x r1y r1z)) (hr2 : 0 < norm (vec3 r2x r2y r2z)) :
    prodRel Encloses Encloses (bdOf Trig.invPi Trig.halfPi e1 e2 r1x r1y r1z r2x r2y r2z)
      (sin (val e1 + val e2) / norm (cross (unit (vec3 r1x r1y r1z)) (unit (vec3 r2x r2y r2z))),
        hval (val e1) (val e2) (norm (cross (unit (vec3 r1x r1y r1z)) (unit (vec3 r2x r2y r2z))))) := by
  have hb := Spec.boundOf.encloses (powLog := Trig.invPi) (powExp := Trig.invPi)
    (encloses_point e1) (encloses_point e2) (encloses_point r1x) (encloses_point r1y)
    (encloses_point r1z) (encloses_point r2x) (encloses_point r2y) (encloses_point r2z)
  have e := boundOf_eq (val e1) (val e2) hr1 hr2
  simp only [vec3_x, vec3_y, vec3_z] at e
  rw [e] at hb
  exact hb

/-- The real value of a float within the endpoints of an accepted interval. -/
theorem In.near {i : Interval} {x y : ℝ} (hx : In i x) (hy : Contains i y) :
    |x - y| ≤ value i.hi.toBits - value i.lo.toBits := by
  obtain ⟨_, _, _, l, u⟩ := hy
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2]

/-- **The error bound of TRIAD's program.**  For a result of status 0, the error bounds and the
references meet the conditions of `triad_error`, and every matrix whose entries lie in the
intervals of the result moves every unit vector by at most `err` from its image under every
attitude that carries each normalized measurement within its error bound of the normalized
reference. -/
theorem triad_bound {b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2 : Float}
    (h : (triad b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2).status = 0) :
    0 ≤ val e1 ∧ 0 ≤ val e2 ∧ val e1 + val e2 < π / 2 ∧
    sin (val e1 + val e2) < norm (cross (unit (vec3 r1x r1y r1z)) (unit (vec3 r2x r2y r2z))) ∧
    ∀ q : Quat, 0 < Quat.norm2 q →
      vangle (attitude q (unit (vec3 b1x b1y b1z))) (unit (vec3 r1x r1y r1z)) ≤ val e1 →
      vangle (attitude q (unit (vec3 b2x b2y b2z))) (unit (vec3 r2x r2y r2z)) ≤ val e2 →
      ∀ M : Mat, InBox (triad b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2) M →
      ∀ v : Vec, dot v v = 1 →
        vangle (M.apply v) (attitude q v) ≤
          val (triad b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2).err := by
  have h' : (triad b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2).status ≠ 1 := by
    rw [h]; decide
  obtain ⟨hb1, hb, hr1, hr, hin⟩ := triad_sound h'
  have hb2 := norm_pos_right hb
  have hr2 := norm_pos_right hr
  have hbd := bdOf_encloses e1 e2 r1x r1y r1z r2x r2y r2z hr1 hr2
  set b1 := vec3 b1x b1y b1z
  set b2 := vec3 b2x b2y b2z
  set r1 := vec3 r1x r1y r1z
  set r2 := vec3 r2x r2y r2z
  set st := norm (cross (unit r1) (unit r2))
  set T := triadMat b1 b2 r1 r2
  -- the estimate's fields
  simp only [triad, triadWith] at h hin ⊢
  generalize Spec.triadOfI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point b1x) (point b1y)
    (point b1z) (point b2x) (point b2y) (point b2z) (point r1x) (point r1y) (point r1z)
    (point r2x) (point r2y) (point r2z) = r at h hin ⊢
  have hne : (finishWith Trig.invPi Trig.halfPi e1 e2 r1x r1y r1z r2x r2y r2z r).status ≠ 1 := by
    rw [h]; decide
  obtain ⟨-, -, he⟩ := finish_cases hne
  rw [he] at h hin ⊢
  simp only at h hin ⊢
  obtain ⟨ge1, ge2, gd, gx, geta, gdhi, gxhi, getahi, gerr, herr⟩ := boundWith_cases h
  rw [herr]
  -- the error bounds
  obtain ⟨pe1, pe2, _⟩ := add_sound gd
  have fe1 := (point_sound pe1).1
  have fe2 := (point_sound pe2).1
  have he1 : 0 ≤ val e1 := by
    have := (le_iff_value zero_value.1 fe1).mp ge1; rwa [zero_value.2] at this
  have he2 : 0 ≤ val e2 := by
    have := (le_iff_value zero_value.1 fe2).mp ge2; rwa [zero_value.2] at this
  have cd := encloses_add (encloses_point e1) (encloses_point e2) gd
  have hd : val e1 + val e2 < π / 2 := by
    have := (le_iff_value cd.2.2.1 lit_three_halves.1).mp gdhi
    rw [lit_three_halves.2] at this
    linarith [cd.2.2.2.2, pi_gt_three]
  have hst : 0 < st := by
    show 0 < norm (cross (unit r1) (unit r2))
    rw [norm_cross_unit hr1 hr2]; positivity
  have hx : sin (val e1 + val e2) < st := by
    have c := hbd.1 gx
    have := c.lt_one_of_hi gxhi
    rwa [div_lt_one hst] at this
  refine ⟨he1, he2, hd, hx, ?_⟩
  intro q hq h1 h2 M hM v hv
  -- TRIAD's error
  have hT := triad_error hb1 hb2 hr1 hr2 he1 he2 hd hx hq h1 h2 hv
  rw [← triadMat_apply] at hT
  -- the box term
  obtain ⟨c11, c12, c13, c21, c22, c23, c31, c32, c33⟩ := hin
  obtain ⟨i11, i12, i13, i21, i22, i23, i31, i32, i33⟩ := hM
  set w : Mat := ⟨val r.2.2.2.2.1.hi - val r.2.2.2.2.1.lo,
    val r.2.2.2.2.2.1.hi - val r.2.2.2.2.2.1.lo,
    val r.2.2.2.2.2.2.1.hi - val r.2.2.2.2.2.2.1.lo,
    val r.2.2.2.2.2.2.2.1.hi - val r.2.2.2.2.2.2.2.1.lo,
    val r.2.2.2.2.2.2.2.2.1.hi - val r.2.2.2.2.2.2.2.2.1.lo,
    val r.2.2.2.2.2.2.2.2.2.1.hi - val r.2.2.2.2.2.2.2.2.2.1.lo,
    val r.2.2.2.2.2.2.2.2.2.2.1.hi - val r.2.2.2.2.2.2.2.2.2.2.1.lo,
    val r.2.2.2.2.2.2.2.2.2.2.2.1.hi - val r.2.2.2.2.2.2.2.2.2.2.2.1.lo,
    val r.2.2.2.2.2.2.2.2.2.2.2.2.hi - val r.2.2.2.2.2.2.2.2.2.2.2.2.lo⟩ with hw
  have hnear : Near M T w := ⟨i11.near c11, i12.near c12, i13.near c13, i21.near c21,
    i22.near c22, i23.near c23, i31.near c31, i32.near c32, i33.near c33⟩
  have hdist := near_dist hnear hv
  have ceta0 := encloses_etaOf r.2.2.2.2.1 r.2.2.2.2.2.1 r.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.1
    r.2.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.2.2.1 r.2.2.2.2.2.2.2.2.2.2.2.1
    r.2.2.2.2.2.2.2.2.2.2.2.2
  rw [← hw] at ceta0
  have ceta := ceta0 geta
  set η := √(Mat.sumSq w)
  have hη0 : 0 ≤ η := Real.sqrt_nonneg _
  have hη : η ≤ 1 / 4 := by
    have := (le_iff_value ceta.2.2.1 lit_quarter.1).mp getahi
    rw [lit_quarter.2] at this
    linarith [ceta.2.2.2.2]
  have hsum : 0 ≤ Mat.sumSq w := by
    have := dot_self_nonneg (sub (M.apply v) (T.apply v)); linarith
  have hTv : dot (T.apply v) (T.apply v) = 1 := by
    rw [triadMat_apply, triad_dot hb1 hb hr1 hr, hv]
  have hB := vangle_near hTv hη0 hη (by rw [Real.sq_sqrt hsum]; exact hdist)
  -- the interval of the bound
  have hx2 : (sin (val e1 + val e2) / st) ^ 2 ≤ 1 := by
    have hsd0 : 0 ≤ sin (val e1 + val e2) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_gt_three])
    rw [div_pow, div_le_one (by positivity), pow_two, pow_two]
    exact (mul_self_lt_mul_self hsd0 hx).le
  have cerr := encloses_errOf hbd.2 hval_nonneg
    (hval_le_one hx2 (by linarith [neg_one_le_cos (val e1)])) ceta0 gerr
  have hle := cerr.2.2.2.2
  calc vangle (M.apply v) (attitude q v)
      ≤ vangle (M.apply v) (T.apply v) + vangle (T.apply v) (attitude q v) :=
        vangle_triangle _ _ _
    _ ≤ arcsin (η / (1 - η)) + 2 * arcsin √(hval (val e1) (val e2) st) := add_le_add hB hT
    _ ≤ _ := by rw [add_comm]; exact hle

end Demos.Attitude
