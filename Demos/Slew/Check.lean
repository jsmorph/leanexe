import Demos.Slew.Decide
import Demos.Slew.Cone
import LeanExe.IR.Combinators

/-! Soundness of the edge check and the static check.  `coneEdge` and `coneStatic` are the checks
of one cone that `edgeOk` and `attitudeOk` evaluate in their loops, which `edgeOk_eq` and
`attitudeOk_eq` state by `rfl`.  `ArcSafe` states the conclusion for a rotation: along the
rotation of the normalized attitude `q̄a` by every angle `φ ∈ [0, θ]` about the axis of `rel`,
every vector within `1.05e-9` of the rotated normalized body vector `b̄` satisfies the cone of the
normalized axis `ū` and cosine `c`, where the axis and angle are those of `rel`'s real value.
`PointSafe` states the same at one attitude.

Past the small-angle threshold, `coneEdge_sound` combines the error bounds with `keepout_arc` or
`keepin_arc`.  A NaN `s` requires `S² ≤ 5 η`, makes a keep-in check fail, and leaves a keep-out
check only the bound at the start, which covers a rotation that small.  Below the threshold, the
slack `2.125 s` exceeds the change `2.0003 S` of the cosine along the rotation (`slack_facts`,
`arc_near_start`).  Every branch bounds the cosine of the unnormalized inputs `1.07e-9` inside
the cone's limit, which covers the normalization error `1.3e-11` and the tube (`finish_out`,
`finish_in`), and `edgeOk_sound` and `attitudeOk_sound` apply the branches to every cone. -/

namespace Demos.Slew.Check

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error Demos.Slew.Axis Demos.Slew.Cone
open Demos.Slew.Normalize Demos.Slew.Arc Demos.Slew.Decide Demos.Slew.Hypot Real
open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx

set_option exponentiation.threshold 4096

/-! ### Definitions -/

/-- A relative quaternion: finite, with a scalar part `w ≥ 0` and a squared norm within `1e-11`
of 1. -/
structure GoodRel (q : Q4) : Prop where
  fw : Fin q.w
  fx : Fin q.x
  fy : Fin q.y
  fz : Fin q.z
  w_nonneg : 0 ≤ val q.w
  norm : |val q.w * val q.w + s2 q - 1| ≤ 1e-11

/-- The check of one cone along the rotation `rel` from `qa`, as `edgeOk` evaluates it. -/
def coneEdge (n : V3) (ct st : Float) (qa : Q4) (b u : V3) (c kind : Float) : Bool :=
  let v0 := qrot qa b
  let nu := dot n u
  let nv := dot n v0
  let f0 := dot u v0
  let aa := f0 - nu * nv
  let bb := dot u (cross n v0)
  let cc := nu * nv
  let f1 := aa * ct + bb * st + cc
  let d1 := bb * ct - aa * st
  let r := Float.sqrt (aa * aa + bb * bb)
  if kind == 0.0 then
    let m1 := max f0 f1
    let m2 := if bb < -eta || d1 > eta then m1 else max m1 (cc + r)
    m2 ≤ c - margin
  else
    let m1 := min f0 f1
    let m2 := if bb > eta || d1 < -eta then m1 else min m1 (cc - r)
    m2 ≥ c + margin

/-- The check of one cone at the attitude `q` with `slack`, as `attitudeOk` evaluates it. -/
def coneStatic (q : Q4) (b u : V3) (c kind slack : Float) : Bool :=
  let f := dot u (qrot q b)
  if kind == 0.0 then f ≤ c - margin - slack else f ≥ c + margin + slack

/-- The axis of `rel`'s real value. -/
noncomputable def axisR (q : Q4) : Vec := Vec.unit (vecPart q)

/-- The rotation angle of `rel`'s real value. -/
noncomputable def angleR (q : Q4) : ℝ := angle (val q.w) (√(s2 q))

/-- The cone holds along the rotation, in a tube of `1.05e-9`. -/
def ArcSafe (qa rel : Q4) (b u : V3) (c kind : Float) : Prop :=
  ∀ φ, 0 ≤ φ → φ ≤ angleR rel → ∀ v : Vec,
    Vec.norm (Vec.sub v (rod (axisR rel) φ (Quat.rot (Quat.unit (quatOf qa)) (Vec.unit (vecOf b))))) ≤
      1.05e-9 → Holds (!(kind == 0.0)) (Vec.unit (vecOf u)) (val c) v

/-! ### The square root `s` -/

theorem ofBits_eq {a b : Float} (h : a.toBits = b.toBits) : a = b := by
  rw [← F64Bits.ofBits_toBits a, ← F64Bits.ofBits_toBits b, h]

theorem sqrt_cases {r : Float} (hr : Fin r) :
    (val r = 0 ∧ Float.sqrt r = r) ∨ (IsNaN (Float.sqrt r) ∧ val r < 0) ∨
      (0 < val r ∧ Fin (Float.sqrt r) ∧
        |val (Float.sqrt r) - √(val r)| ≤ 1 / 2 ^ 53 * √(val r)) := by
  have hbits := F64Bits.toBits_sqrt r
  have hnan := not_nan_of_finite hr
  by_cases hm : Wasm.IEEE64.scaledMagnitude r.toBits = 0
  · left
    have e : Wasm.IEEE64.sqrt r.toBits = r.toBits := by unfold Wasm.IEEE64.sqrt; simp [hnan, hm]
    refine ⟨by simp [val, value, Wasm.IEEE64.scaledValue, hm], ofBits_eq (by rw [hbits, e])⟩
  · by_cases hs : Wasm.IEEE64.sign r.toBits = true
    · right; left
      have e : Wasm.IEEE64.sqrt r.toBits = Wasm.IEEE64.canonicalNaN := by
        unfold Wasm.IEEE64.sqrt; simp [hnan, hm, hs]
      refine ⟨by simp only [IsNaN, hbits, e, canonicalNaN_isNaN], ?_⟩
      simp only [val, value, Wasm.IEEE64.scaledValue, hs, ite_true]
      have : (0 : ℝ) < Wasm.IEEE64.scaledMagnitude r.toBits := by exact_mod_cast Nat.pos_of_ne_zero hm
      push_cast
      rw [neg_div]; linarith [div_pos this (show (0 : ℝ) < 2 ^ 1074 by positivity)]
    · right; right
      have hs' : Wasm.IEEE64.sign r.toBits = false := by simpa using hs
      have hrel := F64SqrtBounds.sqrt_real_relative r.toBits hr hm hs'
      refine ⟨?_, by simp only [Rounding.Fin, hbits]; exact hrel.1, by simp only [val, hbits]; exact hrel.2⟩
      simp only [val, value, Wasm.IEEE64.scaledValue, hs', Bool.false_eq_true, ite_false]
      have : (0 : ℝ) < Wasm.IEEE64.scaledMagnitude r.toBits := by exact_mod_cast Nat.pos_of_ne_zero hm
      positivity

theorem GoodRel.components {q : Q4} (h : GoodRel q) :
    |val q.x| ≤ 1.0001 ∧ |val q.y| ≤ 1.0001 ∧ |val q.z| ≤ 1.0001 ∧ |val q.w| ≤ 1.0001 := by
  have hn := abs_le.mp h.norm
  simp only [s2] at hn
  have b : ∀ t : ℝ, t * t ≤ 1 + 1e-11 → |t| ≤ 1.0001 := by
    intro t ht; rw [abs_le]; constructor <;> nlinarith
  refine ⟨b _ ?_, b _ ?_, b _ ?_, b _ ?_⟩ <;>
    nlinarith [mul_self_nonneg (val q.w), mul_self_nonneg (val q.x), mul_self_nonneg (val q.y),
      mul_self_nonneg (val q.z)]

theorem GoodRel.radApprox {q : Q4} (h : GoodRel q) :
    FApprox (radicand q) (s2 q) (3.001 / 2 ^ 53 * s2 q + 4 / 2 ^ 1075) := by
  obtain ⟨bx, byy, bz, _⟩ := h.components
  exact radicand_approx q h.fx h.fy h.fz (by linarith) (by linarith) (by linarith)

theorem GoodRel.fin_radicand {q : Q4} (h : GoodRel q) : Fin (radicand q) := h.radApprox.1

/-- Past the small-angle threshold, `s` is a NaN or `S² ≥ 2⁻¹⁰⁰⁰`. -/
theorem main_cases {q : Q4} (h : GoodRel q) (hs : ¬ sOf q < Demos.Slew.sMin) :
    IsNaN (sOf q) ∨ 1 / 2 ^ 1000 ≤ s2 q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hnn, hsmall⟩ := hcon
  have hr := h.radApprox
  have hS0 := s2_nonneg q
  have hrv : val (radicand q) ≤ 1 / 2 ^ 999 := by
    have := hr.upper; simp only [val]; nlinarith
  have hmin := sMin_bounds
  apply hs
  rcases sqrt_cases h.fin_radicand with ⟨hz, he⟩ | ⟨hn, _⟩ | ⟨hpos, hfin, hb⟩
  · have hfs : Fin (sOf q) := by simp only [sOf]; rw [he]; exact h.fin_radicand
    rw [lt_iff_val hfs sMin_val.1]
    simp only [sOf]; rw [he, hz]; linarith
  · exact absurd hn hnn
  · simp only [sOf]
    rw [lt_iff_val hfin sMin_val.1]
    have hsq : √(val (radicand q)) ≤ 1 / 2 ^ 499 := by
      rw [show (1 : ℝ) / 2 ^ 499 = √((1 / 2 ^ 499) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num at hrv ⊢; linarith)
    have := (abs_le.mp hb).2
    have h0 := Real.sqrt_nonneg (val (radicand q))
    nlinarith

/-- A NaN `s` comes from a negative radicand, so `S²` is below `5 η`. -/
theorem nan_tiny {q : Q4} (h : GoodRel q) (hn : IsNaN (sOf q)) : s2 q ≤ 5 / 2 ^ 1075 := by
  have hr := h.radApprox
  rcases sqrt_cases h.fin_radicand with ⟨_, he⟩ | ⟨_, hneg⟩ | ⟨_, hfin, _⟩
  · exfalso; simp only [sOf] at hn; rw [he] at hn; exact not_nan_of_fin h.fin_radicand hn
  · have := hr.lower; simp only [val] at hneg; nlinarith [s2_nonneg q]
  · exfalso; exact not_nan_of_fin hfin hn

/-! ### Small rotations -/

theorem rod_zero (n v : Vec) : rod n 0 v = v := by
  ext <;> simp [rod]

theorem angle_zero {w : ℝ} (hw : 0 < w) : angle w 0 = 0 := by
  unfold angle
  rw [show (w * w - 0 * 0) / (w * w + 0 * 0) = 1 by
    rw [mul_zero, sub_zero, add_zero, div_self (by positivity)], arccos_one]

theorem dot_unit_self (a : Vec) (h : 0 < Vec.norm a) : Vec.dot (Vec.unit a) (Vec.unit a) = 1 := by
  have := norm_unit a h
  rw [Vec.norm] at this
  have h0 := dot_self_nonneg (Vec.unit a)
  nlinarith [Real.sq_sqrt h0]

/-- A rotation by `φ ≤ θ` about the axis of `rel` changes the cosine by at most
`‖U‖ ‖V‖ 2 S / √Q`. -/
theorem arc_disp (U V : Vec) {q : Q4} (h : GoodRel q) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ ≤ angleR q) :
    |Vec.dot U (rod (axisR q) φ V) - Vec.dot U V| ≤
      Vec.norm U * Vec.norm V * (2 * √(s2 q) / √(val q.w * val q.w + s2 q)) := by
  set S := √(s2 q)
  set W := val q.w
  have hQ := abs_le.mp h.norm
  have hQpos : 0 < W * W + S * S := by
    rw [show S * S = s2 q from Real.mul_self_sqrt (s2_nonneg q)]; linarith
  by_cases hS : S = 0
  · have hW : 0 < W := by
      rw [hS] at hQpos; nlinarith [h.w_nonneg]
    have hφz : φ = 0 := by
      have : angleR q = 0 := by simp only [angleR]; rw [show √(s2 q) = 0 from hS]; exact angle_zero hW
      linarith
    rw [hφz, rod_zero]; simp only [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (Arc.norm_nonneg U) (Arc.norm_nonneg V))
      (div_nonneg (by positivity) (Real.sqrt_nonneg _))
  · have hSpos : 0 < S := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hS)
    have hN : Vec.dot (axisR q) (axisR q) = 1 := dot_unit_self _ (by rw [norm_vecPart]; exact hSpos)
    have hd := dot_rod_sub_le U (axisR q) V hN φ
    have hθ := angle_le_pi W S
    have hcos : cos (angle W S) ≤ cos φ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hφ0 hθ hφ
    have hc := cos_angle W S hQpos
    have hSS : S * S = s2 q := Real.mul_self_sqrt (s2_nonneg q)
    have e : √(2 - 2 * cos (angle W S)) = 2 * S / √(W * W + s2 q) := by
      rw [hc, ← hSS]
      rw [show 2 - 2 * ((W * W - S * S) / (W * W + S * S)) = (2 * S) ^ 2 / (W * W + S * S) by
        field_simp; ring]
      rw [Real.sqrt_div' _ hQpos.le, Real.sqrt_sq (by positivity)]
    calc |Vec.dot U (rod (axisR q) φ V) - Vec.dot U V|
        ≤ Vec.norm U * Vec.norm V * √(2 - 2 * cos φ) := hd
      _ ≤ Vec.norm U * Vec.norm V * √(2 - 2 * cos (angle W S)) := by
          apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith))
          exact mul_nonneg (Arc.norm_nonneg U) (Arc.norm_nonneg V)
      _ = Vec.norm U * Vec.norm V * (2 * S / √(W * W + s2 q)) := by rw [e]

theorem GoodRel.q_pos {q : Q4} (h : GoodRel q) : 0 < val q.w * val q.w + s2 q := by
  linarith [abs_le.mp h.norm]

theorem GoodRel.q_sqrt {q : Q4} (h : GoodRel q) : 0.99999 ≤ √(val q.w * val q.w + s2 q) := by
  rw [show (0.99999 : ℝ) = √(0.99999 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith [abs_le.mp h.norm])

/-- Along the rotation, the cosine of the unnormalized vectors stays within `2.0003 S` of its
start. -/
theorem arc_near_start {qa rel : Q4} {b u : V3} (hq : GoodQ qa) (hb : GoodV b) (hu : GoodV u)
    (hr : GoodRel rel) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ ≤ angleR rel) :
    |Vec.dot (vecOf u) (rod (axisR rel) φ (Quat.rot (quatOf qa) (vecOf b))) -
      Vec.dot (vecOf u) (Quat.rot (quatOf qa) (vecOf b))| ≤ 2.0003 * √(s2 rel) := by
  have hd := arc_disp (vecOf u) (Quat.rot (quatOf qa) (vecOf b)) hr hφ0 hφ
  have hUn := hu.norm_le
  have hVn := norm_rot_le (quatOf qa) (vecOf b) hq.norm hb.norm
  have hQ := hr.q_sqrt
  have hS := Real.sqrt_nonneg (s2 rel)
  have hV0 := Arc.norm_nonneg (Quat.rot (quatOf qa) (vecOf b))
  refine hd.trans ?_
  have e : 2 * √(s2 rel) / √(val rel.w * val rel.w + s2 rel) ≤ 2 * √(s2 rel) / 0.99999 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hQ
  calc Vec.norm (vecOf u) * Vec.norm (Quat.rot (quatOf qa) (vecOf b)) *
        (2 * √(s2 rel) / √(val rel.w * val rel.w + s2 rel))
      ≤ (1 + 3e-12) * 1.0001 * (2 * √(s2 rel) / 0.99999) :=
        mul_le_mul (mul_le_mul hUn hVn hV0 (by norm_num)) e (by positivity) (by norm_num)
    _ = (1 + 3e-12) * 1.0001 * 2 / 0.99999 * √(s2 rel) := by ring
    _ ≤ 2.0003 * √(s2 rel) := mul_le_mul_of_nonneg_right (by norm_num) hS

/-- Either the axis of `rel` has unit length or the rotation angle is zero. -/
theorem axis_or_zero {q : Q4} (h : GoodRel q) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ ≤ angleR q) :
    Vec.dot (axisR q) (axisR q) = 1 ∨ φ = 0 := by
  by_cases hS : √(s2 q) = 0
  · right
    have hS2 : s2 q = 0 := by
      have := Real.mul_self_sqrt (s2_nonneg q)
      rw [hS] at this
      linarith
    have hW : 0 < val q.w := by nlinarith [h.w_nonneg, h.q_pos]
    have : angleR q = 0 := by simp only [angleR]; rw [hS]; exact angle_zero hW
    linarith
  · left
    exact dot_unit_self (vecPart q)
      (by rw [norm_vecPart]; exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hS))

/-! ### From the unnormalized cosine to the cone -/

theorem spec_close' (U B : Vec) (Q : Quat) (N : Vec) (φ : ℝ) (hN : Vec.dot N N = 1 ∨ φ = 0)
    (hU : |Vec.dot U U - 1| ≤ 3e-12) (hB : |Vec.dot B B - 1| ≤ 3e-12)
    (hQ : |Quat.norm2 Q - 1| ≤ 3e-12) :
    |Vec.dot (Vec.unit U) (rod N φ (Quat.rot (Quat.unit Q) (Vec.unit B))) -
      Vec.dot U (rod N φ (Quat.rot Q B))| ≤ 1.3e-11 := by
  rcases hN with hN | rfl
  · exact spec_close U B Q N φ hN hU hB hQ
  · have h := spec_close U B Q ⟨1, 0, 0⟩ 0 (by norm_num [Vec.dot]) hU hB hQ
    simp only [rod_zero] at h ⊢
    exact h

theorem holds_false (U : Vec) (c : ℝ) (v : Vec) : Holds false U c v ↔ Vec.dot U v ≤ c := by
  simp [Holds]

theorem holds_true (U : Vec) (c : ℝ) (v : Vec) : Holds true U c v ↔ c ≤ Vec.dot U v := by
  simp [Holds]

/-- A keep-out bound of `c - 1.07e-9` on the unnormalized cosine covers normalization and the
tube. -/
theorem finish_out {qa : Q4} {b u : V3} (hq : GoodQ qa) (hb : GoodV b) (hu : GoodV u) {N : Vec}
    {φ c : ℝ} (hN : Vec.dot N N = 1 ∨ φ = 0)
    (hg : Vec.dot (vecOf u) (rod N φ (Quat.rot (quatOf qa) (vecOf b))) ≤ c - 1.07e-9) (v : Vec)
    (hv : Vec.norm (Vec.sub v (rod N φ (Quat.rot (Quat.unit (quatOf qa)) (Vec.unit (vecOf b))))) ≤
      1.05e-9) :
    Vec.dot (Vec.unit (vecOf u)) v ≤ c := by
  have hs := abs_le.mp (spec_close' (vecOf u) (vecOf b) (quatOf qa) N φ hN hu.norm hb.norm hq.norm)
  have hn := near_bounds (Vec.unit (vecOf u)) _ v 1.05e-9
    (Arc.norm_unit _ (norm_near_one (vecOf u) 3e-12 (by norm_num) hu.norm).2) hv
  linarith [hn.1]

/-- The keep-in mirror of `finish_out`. -/
theorem finish_in {qa : Q4} {b u : V3} (hq : GoodQ qa) (hb : GoodV b) (hu : GoodV u) {N : Vec}
    {φ c : ℝ} (hN : Vec.dot N N = 1 ∨ φ = 0)
    (hg : c + 1.07e-9 ≤ Vec.dot (vecOf u) (rod N φ (Quat.rot (quatOf qa) (vecOf b)))) (v : Vec)
    (hv : Vec.norm (Vec.sub v (rod N φ (Quat.rot (Quat.unit (quatOf qa)) (Vec.unit (vecOf b))))) ≤
      1.05e-9) :
    c ≤ Vec.dot (Vec.unit (vecOf u)) v := by
  have hs := abs_le.mp (spec_close' (vecOf u) (vecOf b) (quatOf qa) N φ hN hu.norm hb.norm hq.norm)
  have hn := near_bounds (Vec.unit (vecOf u)) _ v 1.05e-9
    (Arc.norm_unit _ (norm_near_one (vecOf u) 3e-12 (by norm_num) hu.norm).2) hv
  linarith [hn.2]

/-! ### Decisions -/

theorem nan_not_lt {a : Float} (h : IsNaN a) (b : Float) : ¬ a < b := by
  rw [F64Bits.lt_iff]; unfold Wasm.IEEE64.lt; simp [show Wasm.IEEE64.isNaN a.toBits = true from h]

theorem val_le_max_left (a b : Float) : val a ≤ val (max a b) := by
  rw [max_def']
  by_cases hab : a ≤ b
  · rw [ite_eq_left hab]; exact le_val_of_le hab
  · exact le_of_eq (congrArg val (ite_eq_right hab).symm)

theorem keepout_f0 {f0 f1 x L : Float} {e : Bool}
    (h : (if e = true then max f0 f1 else max (max f0 f1) x) ≤ L) : val f0 ≤ val L := by
  cases e
  · rw [ite_eq_right Bool.false_ne_true] at h
    exact (val_le_max_left f0 f1).trans (val_le_of_max_le h)
  · rw [ite_eq_left rfl] at h
    exact val_le_of_max_le h

theorem keepout_facts {f0 f1 x L : Float} {e : Bool} (hf0 : Fin f0) (hf1 : Fin f1)
    (h : (if e = true then max f0 f1 else max (max f0 f1) x) ≤ L) :
    val f0 ≤ val L ∧ val f1 ≤ val L ∧ (e = false → Fin x → val x ≤ val L) := by
  have hm := max_val hf0 hf1
  cases e
  · rw [ite_eq_right Bool.false_ne_true] at h
    have hmx := val_le_of_max_le h
    rw [hm.2] at hmx
    exact ⟨(le_max_left _ _).trans hmx, (le_max_right _ _).trans hmx,
      fun _ hx => val_le_of_max_le_right hm.1 hx h⟩
  · rw [ite_eq_left rfl] at h
    exact ⟨val_le_of_max_le h, val_le_of_max_le_right hf0 hf1 h, fun h' => absurd h' (by decide)⟩

theorem keepin_facts {f0 f1 x L : Float} {e : Bool} (hf0 : Fin f0) (hf1 : Fin f1)
    (h : L ≤ (if e = true then min f0 f1 else min (min f0 f1) x)) :
    val L ≤ val f0 ∧ val L ≤ val f1 ∧ (e = false → Fin x → val L ≤ val x) := by
  have hm := min_val hf0 hf1
  cases e
  · rw [ite_eq_right Bool.false_ne_true] at h
    have hmn : val L ≤ val (min f0 f1) := by
      rcases val_le_of_le_min_left hm.1 h with h1 | ⟨h1, h2⟩
      · exact h1
      · linarith
    rw [hm.2] at hmn
    exact ⟨hmn.trans (min_le_left _ _), hmn.trans (min_le_right _ _),
      fun _ hx => (val_le_of_le_min hm.1 hx h).2⟩
  · rw [ite_eq_left rfl] at h
    exact ⟨(val_le_of_le_min hf0 hf1 h).1, (val_le_of_le_min hf0 hf1 h).2,
      fun h' => absurd h' (by decide)⟩

/-- A keep-in check with a NaN `f₁` and a NaN stationary value fails. -/
theorem keepin_nan {f0 f1 x L : Float} {e : Bool} (hf1 : IsNaN f1) (hx : IsNaN x)
    (h : L ≤ (if e = true then min f0 f1 else min (min f0 f1) x)) : False := by
  rw [hf1.min_right] at h
  cases e
  · rw [ite_eq_right Bool.false_ne_true, hf1.min_left] at h
    exact hx.not_le_right L h
  · rw [ite_eq_left rfl] at h
    exact hf1.not_le_right L h

/-! ### Limits -/

theorem margin_bnd : Bnd margin (val margin) 0 1.1e-9 :=
  Bnd.of_val margin_val.1 (abs_le.mpr ⟨by linarith [margin_bounds.1], margin_bounds.2⟩)

theorem low_limit {c : Float} (hc : Fin c) (hc1 : |val c| ≤ 1) :
    Bnd (c - margin) (val c - val margin) (1.01 / 2 ^ 53) (1 + 1.1e-9) :=
  Bnd.sub (1.01 / 2 ^ 53) (Bnd.of_val hc hc1) margin_bnd (by norm_num) (by norm_num)

theorem high_limit {c : Float} (hc : Fin c) (hc1 : |val c| ≤ 1) :
    Bnd (c + margin) (val c + val margin) (1.01 / 2 ^ 53) (1 + 1.1e-9) :=
  Bnd.add (1.01 / 2 ^ 53) (Bnd.of_val hc hc1) margin_bnd (by norm_num) (by norm_num)

theorem f0_bnd {qa : Q4} {b u : V3} (hq : GoodQ qa) (hb : GoodV b) (hu : GoodV u) :
    Bnd (dot u (qrot qa b)) (Vec.dot (vecOf u) (Quat.rot (quatOf qa) (vecOf b))) (233.5 / 2 ^ 53)
      1.0002 := by
  have f0 := dot_bnd (76.1 / 2 ^ 53) (154.3 / 2 ^ 53) (233.5 / 2 ^ 53) hu.bnd (v0_bnd hq hb)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hUn := hu.norm_le
  have hVn := norm_rot_le (quatOf qa) (vecOf b) hq.norm hb.norm
  refine f0.rebound ((abs_dot_le _ _).trans ?_)
  nlinarith [Arc.norm_nonneg (vecOf u), Arc.norm_nonneg (Quat.rot (quatOf qa) (vecOf b))]

/-! ### The edge check past the small-angle threshold -/

/-- The amplitude when the computed `a² + b²` is below `2⁻¹⁰⁰⁰`. -/
theorem small_amplitude {aa bb : Float} {A B : ℝ} (haa : Bnd aa A (509.6 / 2 ^ 53) 2.0005)
    (hbb : Bnd bb B (503 / 2 ^ 53) 1.0003) (h : val aa * val aa + val bb * val bb < 1 / 2 ^ 1000) :
    √(A ^ 2 + B ^ 2) ≤ 1014 / 2 ^ 53 := by
  have ea : |val aa - A| ≤ 509.6 / 2 ^ 53 := haa.1.2
  have eb : |val bb - B| ≤ 503 / 2 ^ 53 := hbb.1.2
  have ha := sq_le_sq' (abs_le.mp ea).1 (abs_le.mp ea).2
  have hb := sq_le_sq' (abs_le.mp eb).1 (abs_le.mp eb).2
  rw [show (1014 : ℝ) / 2 ^ 53 = √((1014 / 2 ^ 53) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (A - 2 * val aa), sq_nonneg (B - 2 * val bb)])

/-- An accepted keep-out check bounds the unnormalized cosine over the rotation. -/
theorem keepout_core {f0 f1 aa bb cc d1 c : Float} {A B C CT ST Q θ φ : ℝ}
    (hθ : θ ≤ π) (hQ : 0 < Q) (hcos : cos θ = CT / Q) (hsin : sin θ = ST / Q)
    (hQ1 : |1 - Q| ≤ 1e-11) (hR : √(A ^ 2 + B ^ 2) ≤ 2.24)
    (hf0 : Bnd f0 (A + C) (233.5 / 2 ^ 53) 1.0002) (hbb : Bnd bb B (503 / 2 ^ 53) 1.0003)
    (hcc : Bnd cc C (274 / 2 ^ 53) 1.0003) (haa : Bnd aa A (509.6 / 2 ^ 53) 2.0005)
    (hf1 : Bnd f1 (A * CT + B * ST + C) (1334.5 / 2 ^ 53) 4.0015)
    (hd1 : Bnd d1 (B * CT - A * ST) (1056.4 / 2 ^ 53) 3.0012) (hc : Fin c) (hc1 : |val c| ≤ 1)
    (h : (if (decide (bb < -eta) || decide (d1 > eta)) = true then max f0 f1
      else max (max f0 f1) (cc + Float.sqrt (aa * aa + bb * bb))) ≤ c - margin)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ θ) :
    A * cos φ + B * sin φ + C ≤ val c - 1.07e-9 := by
  obtain ⟨h0, h1, hx⟩ := keepout_facts hf0.1.1 hf1.1.1 h
  have hL := (low_limit hc hc1).upper
  have hm := margin_bounds
  have he := eta_bounds
  have hdec : (B ≤ 0 ∨ 0 ≤ B * CT - A * ST) ∨
      C + √(A ^ 2 + B ^ 2) ≤ val c - val margin + 2300 / 2 ^ 53 := by
    cases hed : (decide (bb < -eta) || decide (d1 > eta))
    · right
      have hx' := hx hed
      by_cases hbig : 1 / 2 ^ 1000 ≤ val aa * val aa + val bb * val bb
      · have hs := Bnd.add (1298 / 2 ^ 53) hcc (hypot_bnd haa hbb le_rfl le_rfl hbig)
          (by norm_num) (by norm_num)
        linarith [hs.lower, hx' hs.1.1]
      · have hR' := small_amplitude haa hbb (not_le.mp hbig)
        have hA := Real.abs_le_sqrt (show A ^ 2 ≤ A ^ 2 + B ^ 2 by nlinarith [sq_nonneg B])
        linarith [abs_le.mp hA, hf0.lower]
    · left
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hed
      rcases hed with hb | hd
      · left
        have := lt_val_of_lt hb
        rw [(neg_val eta_val.1).2] at this
        linarith [hbb.lower]
      · right
        have := lt_val_of_lt hd
        linarith [hd1.upper]
  have h0r : A + C ≤ val c - val margin + 2300 / 2 ^ 53 := by linarith [hf0.lower]
  have h1r : A * CT + B * ST + C ≤ val c - val margin + 2300 / 2 ^ 53 := by linarith [hf1.lower]
  have := keepout_arc hθ hQ hcos hsin hQ1 hR h0r h1r hdec hφ0 hφ
  linarith

/-- An accepted keep-in check bounds the unnormalized cosine over the rotation from below. -/
theorem keepin_core {f0 f1 aa bb cc d1 c : Float} {A B C CT ST Q θ φ : ℝ}
    (hθ : θ ≤ π) (hQ : 0 < Q) (hcos : cos θ = CT / Q) (hsin : sin θ = ST / Q)
    (hQ1 : |1 - Q| ≤ 1e-11) (hR : √(A ^ 2 + B ^ 2) ≤ 2.24)
    (hf0 : Bnd f0 (A + C) (233.5 / 2 ^ 53) 1.0002) (hbb : Bnd bb B (503 / 2 ^ 53) 1.0003)
    (hcc : Bnd cc C (274 / 2 ^ 53) 1.0003) (haa : Bnd aa A (509.6 / 2 ^ 53) 2.0005)
    (hf1 : Bnd f1 (A * CT + B * ST + C) (1334.5 / 2 ^ 53) 4.0015)
    (hd1 : Bnd d1 (B * CT - A * ST) (1056.4 / 2 ^ 53) 3.0012) (hc : Fin c) (hc1 : |val c| ≤ 1)
    (h : c + margin ≤ (if (decide (bb > eta) || decide (d1 < -eta)) = true then min f0 f1
      else min (min f0 f1) (cc - Float.sqrt (aa * aa + bb * bb))))
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ θ) :
    val c + 1.07e-9 ≤ A * cos φ + B * sin φ + C := by
  obtain ⟨h0, h1, hx⟩ := keepin_facts hf0.1.1 hf1.1.1 h
  have hL := (high_limit hc hc1).lower
  have hm := margin_bounds
  have he := eta_bounds
  have hdec : (0 ≤ B ∨ B * CT - A * ST ≤ 0) ∨
      val c + val margin - 2300 / 2 ^ 53 ≤ C - √(A ^ 2 + B ^ 2) := by
    cases hed : (decide (bb > eta) || decide (d1 < -eta))
    · right
      have hx' := hx hed
      by_cases hbig : 1 / 2 ^ 1000 ≤ val aa * val aa + val bb * val bb
      · have hs := Bnd.sub (1298 / 2 ^ 53) hcc (hypot_bnd haa hbb le_rfl le_rfl hbig)
          (by norm_num) (by norm_num)
        linarith [hs.upper, hx' hs.1.1]
      · have hR' := small_amplitude haa hbb (not_le.mp hbig)
        have hA := Real.abs_le_sqrt (show A ^ 2 ≤ A ^ 2 + B ^ 2 by nlinarith [sq_nonneg B])
        linarith [abs_le.mp hA, hf0.upper]
    · left
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hed
      rcases hed with hb | hd
      · left
        have := lt_val_of_lt hb
        linarith [hbb.upper]
      · right
        have := lt_val_of_lt hd
        rw [(neg_val eta_val.1).2] at this
        linarith [hd1.lower]
  have h0r : val c + val margin - 2300 / 2 ^ 53 ≤ A + C := by linarith [hf0.upper]
  have h1r : val c + val margin - 2300 / 2 ^ 53 ≤ A * CT + B * ST + C := by linarith [hf1.upper]
  have := keepin_arc hθ hQ hcos hsin hQ1 hR h0r h1r hdec hφ0 hφ
  linarith

/-- The program's axis of the rotation `rel`. -/
def axisF (q : Q4) : V3 := ⟨q.x / sOf q, q.y / sOf q, q.z / sOf q⟩

/-- Past the small-angle threshold, an accepted check of one cone keeps the cone along the
rotation. -/
theorem coneEdge_sound {qa rel : Q4} {b u : V3} {c kind : Float} (hq : GoodQ qa) (hb : GoodV b)
    (hu : GoodV u) (hc : Fin c) (hc1 : |val c| ≤ 1) (hr : GoodRel rel) (hs : ¬ sOf rel < sMin)
    (h : coneEdge (axisF rel) (rel.w * rel.w - sOf rel * sOf rel) (2.0 * rel.w * sOf rel) qa b u c
      kind = true) :
    ArcSafe qa rel b u c kind := by
  intro φ hφ0 hφ v hv
  have hNφ := axis_or_zero hr hφ0 hφ
  simp only [coneEdge] at h
  rcases main_cases hr hs with hnan | hbig
  · by_cases hk : (kind == 0.0) = true
    · rw [ite_eq_left hk] at h
      have h0 := keepout_f0 (of_decide_eq_true h)
      rw [hk, Bool.not_true, holds_false]
      refine finish_out hq hb hu hNφ ?_ v hv
      have f0 := f0_bnd hq hb hu
      have hL := (low_limit hc hc1).upper
      have hS : √(s2 rel) ≤ 1e-100 := by
        rw [show (1e-100 : ℝ) = √((1e-100) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt ((nan_tiny hr hnan).trans (by norm_num))
      have hd := abs_le.mp (arc_near_start hq hb hu hr hφ0 hφ)
      linarith [f0.lower, margin_bounds.1]
    · rw [ite_eq_right hk] at h
      exfalso
      have hx : IsNaN (axisF rel).x := hnan.div_right rel.x
      have hcc := (IsNaN.dot hx u).mul_left (dot (axisF rel) (qrot qa b))
      exact keepin_nan (hcc.add_right _) (hcc.sub_left _) (of_decide_eq_true h)
  · obtain ⟨bx, byy, bz, bw⟩ := hr.components
    have hSpos : 0 < √(s2 rel) := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) hbig)
    have hSS : √(s2 rel) * √(s2 rel) = s2 rel := Real.mul_self_sqrt (s2_nonneg rel)
    have hQn := abs_le.mp hr.norm
    have hS1 : √(s2 rel) ≤ 1.0001 := by nlinarith [mul_self_nonneg (val rel.w)]
    have hsa := s_approx rel hr.fx hr.fy hr.fz (by linarith) (by linarith) (by linarith) hbig
    have hsB : Bnd (sOf rel) (√(s2 rel)) (4.2 / 2 ^ 53) 1.0001 :=
      ⟨Approx.mono hsa (by nlinarith), by rw [abs_of_pos hSpos]; exact hS1⟩
    have hQ1 : val rel.w * val rel.w + √(s2 rel) * √(s2 rel) ≤ 1.0001 := by rw [hSS]; linarith
    have hn : Bnd3 (axisF rel) (axisR rel) (5.2 / 2 ^ 53) 1 :=
      axis_bnd rel hr.fx hr.fy hr.fz hSpos hsa
    have hN : Vec.dot (axisR rel) (axisR rel) = 1 :=
      dot_unit_self (vecPart rel) (by rw [norm_vecPart]; exact hSpos)
    obtain ⟨f0, bb, cc, aa, f1, d1⟩ := cone_values hq hb hu hn hN
      (ct_bnd (Bnd.of_val hr.fw bw) hsB hQ1) (st_bnd (Bnd.of_val hr.fw bw) hsB hQ1)
    have hQpos : 0 < val rel.w * val rel.w + √(s2 rel) * √(s2 rel) := by
      rw [hSS]; exact hr.q_pos
    have hcos := cos_angle (val rel.w) (√(s2 rel)) hQpos
    have hsin := sin_angle (val rel.w) (√(s2 rel)) hr.w_nonneg hSpos.le hQpos
    have hQ1' : |1 - (val rel.w * val rel.w + √(s2 rel) * √(s2 rel))| ≤ 1e-11 := by
      rw [hSS, abs_sub_comm]; exact hr.norm
    have hUV : Vec.norm (vecOf u) * Vec.norm (Quat.rot (quatOf qa) (vecOf b)) ≤ 2.24 := by
      have := mul_le_mul hu.norm_le (norm_rot_le (quatOf qa) (vecOf b) hq.norm hb.norm)
        (Arc.norm_nonneg _) (by norm_num)
      linarith
    have hR := (sinusoid_amplitude_le (vecOf u) (axisR rel)
      (Quat.rot (quatOf qa) (vecOf b)) hN).trans hUV
    by_cases hk : (kind == 0.0) = true
    · rw [ite_eq_left hk] at h
      rw [hk, Bool.not_true, holds_false]
      refine finish_out hq hb hu hNφ ?_ v hv
      rw [dot_rod]
      exact keepout_core (angle_le_pi _ _) hQpos hcos hsin hQ1' hR
        (by rw [sub_add_cancel]; exact f0) bb cc aa f1 d1 hc hc1 (of_decide_eq_true h) hφ0 hφ
    · rw [ite_eq_right hk] at h
      rw [Bool.not_eq_true] at hk
      rw [hk, Bool.not_false, holds_true]
      refine finish_in hq hb hu hNφ ?_ v hv
      rw [dot_rod]
      exact keepin_core (angle_le_pi _ _) hQpos hcos hsin hQ1' hR
        (by rw [sub_add_cancel]; exact f0) bb cc aa f1 d1 hc hc1 (of_decide_eq_true h) hφ0 hφ

/-! ### The static check -/

theorem zero_bits : (0.0 : Float).toBits = 0 := rfl

theorem zero_val : Fin (0.0 : Float) ∧ val (0.0 : Float) = 0 := by
  have hs : Wasm.IEEE64.scaledValue 0 = 0 := by decide +kernel
  refine ⟨?_, ?_⟩
  · simp only [Rounding.Fin, zero_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, zero_bits, value, hs]; simp

/-- An accepted keep-out check of the start attitude with `slack`. -/
theorem static_out {q : Q4} {b u : V3} {c slack : Float} (hq : GoodQ q) (hb : GoodV b)
    (hu : GoodV u) (hc : Fin c) (hc1 : |val c| ≤ 1) (hsl : Fin slack) (hsl1 : |val slack| ≤ 1e-6)
    (h : dot u (qrot q b) ≤ c - margin - slack) :
    Vec.dot (vecOf u) (Quat.rot (quatOf q) (vecOf b)) ≤ val c - val slack - 1.0998e-9 := by
  have f0 := f0_bnd hq hb hu
  have hl := Bnd.sub (2.1 / 2 ^ 53) (low_limit hc hc1) (Bnd.of_val hsl hsl1) (by norm_num)
    (by norm_num)
  have h1 := le_val_of_le h
  linarith [f0.lower, hl.upper, margin_bounds.1]

/-- An accepted keep-in check of the start attitude with `slack`. -/
theorem static_in {q : Q4} {b u : V3} {c slack : Float} (hq : GoodQ q) (hb : GoodV b)
    (hu : GoodV u) (hc : Fin c) (hc1 : |val c| ≤ 1) (hsl : Fin slack) (hsl1 : |val slack| ≤ 1e-6)
    (h : dot u (qrot q b) ≥ c + margin + slack) :
    val c + val slack + 1.0998e-9 ≤ Vec.dot (vecOf u) (Quat.rot (quatOf q) (vecOf b)) := by
  have f0 := f0_bnd hq hb hu
  have hl := Bnd.add (2.1 / 2 ^ 53) (high_limit hc hc1) (Bnd.of_val hsl hsl1) (by norm_num)
    (by norm_num)
  have h1 := le_val_of_le h
  linarith [f0.upper, hl.lower, margin_bounds.1]

/-- Below the small-angle threshold, `s` is finite, non-negative, and below `1.0001e-7`. -/
theorem s_facts {q : Q4} (h : GoodRel q) (hs : sOf q < sMin) :
    Fin (sOf q) ∧ 0 ≤ val (sOf q) ∧ val (sOf q) < 1.0001e-7 := by
  have hlt : val (sOf q) < 1.0001e-7 := by linarith [lt_val_of_lt hs, sMin_bounds.2]
  rcases sqrt_cases h.fin_radicand with ⟨hz, he⟩ | ⟨hn, _⟩ | ⟨_, hfin, hb⟩
  · have hfs : Fin (sOf q) := by simp only [sOf]; rw [he]; exact h.fin_radicand
    have hv : val (sOf q) = 0 := by simp only [sOf]; rw [he, hz]
    exact ⟨hfs, hv.ge, hlt⟩
  · exact absurd hs (nan_not_lt hn _)
  · refine ⟨hfin, ?_, hlt⟩
    have := (abs_le.mp hb).1
    have h0 := Real.sqrt_nonneg (val (radicand q))
    simp only [sOf]
    linarith

theorem s_lower {q : Q4} (h : GoodRel q) (hnn : 0 ≤ val (sOf q)) :
    √(s2 q) * (1 - 4.1 / 2 ^ 53) - 1 / 2 ^ 500 ≤ val (sOf q) := by
  have hS0 := Real.sqrt_nonneg (s2 q)
  by_cases hbig : 1 / 2 ^ 1000 ≤ s2 q
  · obtain ⟨bx, byy, bz, _⟩ := h.components
    have hl : √(s2 q) - 4.1 / 2 ^ 53 * √(s2 q) ≤ val (sOf q) :=
      (s_approx q h.fx h.fy h.fz (by linarith) (by linarith) (by linarith) hbig).lower
    linarith
  · have hS : √(s2 q) ≤ 1 / 2 ^ 500 := by
      rw [show (1 : ℝ) / 2 ^ 500 = √((1 / 2 ^ 500) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num at hbig ⊢; linarith)
    nlinarith

/-- The slack `2.125 s` of the small-angle branch covers the rotation. -/
theorem slack_facts {q : Q4} (h : GoodRel q) (hs : sOf q < sMin) :
    Fin (2.125 * sOf q) ∧ |val (2.125 * sOf q)| ≤ 1e-6 ∧
      2.0003 * √(s2 q) - 1e-20 ≤ val (2.125 * sOf q) := by
  obtain ⟨hfin, hnn, hlt⟩ := s_facts h hs
  have hlo := s_lower h hnn
  have h8 : Bnd (2.125 : Float) (17 / 8) 0 (17 / 8) := by
    have := Bnd.of_val twoEighth_val.1 (M := 17 / 8) (by rw [twoEighth_val.2]; norm_num)
    rwa [twoEighth_val.2] at this
  have hsB : Bnd (sOf q) (val (sOf q)) 0 1.0001e-7 :=
    Bnd.of_val hfin (by rw [abs_of_nonneg hnn]; exact hlt.le)
  have hm := Bnd.mul 1e-22 h8 hsB (by norm_num) (by norm_num)
  have hS0 := Real.sqrt_nonneg (s2 q)
  refine ⟨hm.1.1, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith [hm.lower, hm.upper]
  · linarith [hm.lower]

/-- Below the small-angle threshold, an accepted check of the start attitude with slack `2.125 s`
keeps the cone along the rotation. -/
theorem coneStatic_edge {qa rel : Q4} {b u : V3} {c kind : Float} (hq : GoodQ qa) (hb : GoodV b)
    (hu : GoodV u) (hc : Fin c) (hc1 : |val c| ≤ 1) (hr : GoodRel rel) (hs : sOf rel < sMin)
    (h : coneStatic qa b u c kind (2.125 * sOf rel) = true) :
    ArcSafe qa rel b u c kind := by
  intro φ hφ0 hφ v hv
  have hNφ := axis_or_zero hr hφ0 hφ
  obtain ⟨hsl, hsl1, hsl2⟩ := slack_facts hr hs
  have hd := abs_le.mp (arc_near_start hq hb hu hr hφ0 hφ)
  simp only [coneStatic] at h
  by_cases hk : (kind == 0.0) = true
  · rw [ite_eq_left hk] at h
    have h' := static_out hq hb hu hc hc1 hsl hsl1 (of_decide_eq_true h)
    rw [hk, Bool.not_true, holds_false]
    refine finish_out hq hb hu hNφ ?_ v hv
    linarith
  · rw [ite_eq_right hk] at h
    have h' := static_in hq hb hu hc hc1 hsl hsl1 (of_decide_eq_true h)
    rw [Bool.not_eq_true] at hk
    rw [hk, Bool.not_false, holds_true]
    refine finish_in hq hb hu hNφ ?_ v hv
    linarith

/-- Every vector within `1.05e-9` of the normalized body vector `b̄` rotated by the normalized
attitude `q̄` satisfies the cone of the normalized axis `ū` and cosine `c`. -/
def PointSafe (q : Q4) (b u : V3) (c kind : Float) : Prop :=
  ∀ v : Vec, Vec.norm (Vec.sub v (Quat.rot (Quat.unit (quatOf q)) (Vec.unit (vecOf b)))) ≤
    1.05e-9 → Holds (!(kind == 0.0)) (Vec.unit (vecOf u)) (val c) v

/-- An accepted check of one cone at an attitude, without slack. -/
theorem coneStatic_point {q : Q4} {b u : V3} {c kind : Float} (hq : GoodQ q) (hb : GoodV b)
    (hu : GoodV u) (hc : Fin c) (hc1 : |val c| ≤ 1) (h : coneStatic q b u c kind 0.0 = true) :
    PointSafe q b u c kind := by
  intro v hv
  rw [← rod_zero ⟨1, 0, 0⟩ (Quat.rot (Quat.unit (quatOf q)) (Vec.unit (vecOf b)))] at hv
  have h0 : |val (0.0 : Float)| ≤ 1e-6 := by rw [zero_val.2]; norm_num
  simp only [coneStatic] at h
  by_cases hk : (kind == 0.0) = true
  · rw [ite_eq_left hk] at h
    have h' := static_out hq hb hu hc hc1 zero_val.1 h0 (of_decide_eq_true h)
    rw [zero_val.2] at h'
    rw [hk, Bool.not_true, holds_false]
    refine finish_out hq hb hu (Or.inr rfl) ?_ v hv
    rw [rod_zero]
    linarith
  · rw [ite_eq_right hk] at h
    have h' := static_in hq hb hu hc hc1 zero_val.1 h0 (of_decide_eq_true h)
    rw [zero_val.2] at h'
    rw [Bool.not_eq_true] at hk
    rw [hk, Bool.not_false, holds_true]
    refine finish_in hq hb hu (Or.inr rfl) ?_ v hv
    rw [rod_zero]
    linarith

/-! ### The loops -/

/-- An accepted loop of the form of `edgeOk` and `attitudeOk` accepts every index. -/
theorem loop_all {n : UInt64} {P : UInt64 → Bool}
    (h : LeanExe.loop n true (fun k ok => if !ok then false else P k) = true) :
    ∀ k : Nat, k < n.toNat → P (UInt64.ofNat k) = true := by
  have key := LeanExe.IR.loop_induction (n := n) (init := true)
    (f := fun k ok => if !ok then false else P k)
    (fun m s => s = true → ∀ k, k < m → P (UInt64.ofNat k) = true)
    (fun _ k hk => absurd hk (Nat.not_lt_zero k))
    (fun m s _ ih hs k hk => by
      cases s with
      | false => simp at hs
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hs
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
        · exact ih rfl k hk
        · exact hs)
  exact key h

/-- The body vector, cone axis, cosine, and kind of cone `k`. -/
def coneBody (xs : Array Float) (d : Dims) (k : UInt64) : V3 :=
  v3At xs (16 + 3 * (rd xs (d.coneOff + 6 * k)).toUInt64)
def coneAxis (xs : Array Float) (d : Dims) (k : UInt64) : V3 := v3At xs (d.coneOff + 6 * k + 1)
def coneCos (xs : Array Float) (d : Dims) (k : UInt64) : Float := rd xs (d.coneOff + 6 * k + 4)
def coneKind (xs : Array Float) (d : Dims) (k : UInt64) : Float := rd xs (d.coneOff + 6 * k + 5)

/-- Cone `k` has a good body vector and axis and a finite cosine in `[-1, 1]`. -/
structure ConeGood (xs : Array Float) (d : Dims) (k : UInt64) : Prop where
  body : GoodV (coneBody xs d k)
  axis : GoodV (coneAxis xs d k)
  fin : Fin (coneCos xs d k)
  cos : |val (coneCos xs d k)| ≤ 1

theorem attitudeOk_eq (xs : Array Float) (d : Dims) (q : Q4) (slack : Float) :
    attitudeOk xs d q slack = LeanExe.loop d.nc true (fun k ok => if !ok then false else
      coneStatic q (coneBody xs d k) (coneAxis xs d k) (coneCos xs d k) (coneKind xs d k) slack) :=
  rfl

theorem edgeOk_eq (xs : Array Float) (d : Dims) (qa rel : Q4) :
    edgeOk xs d qa rel =
      if sOf rel < sMin then
        LeanExe.loop d.nc true (fun k ok => if !ok then false else
          coneStatic qa (coneBody xs d k) (coneAxis xs d k) (coneCos xs d k) (coneKind xs d k)
            (2.125 * sOf rel))
      else
        LeanExe.loop d.nc true (fun k ok => if !ok then false else
          coneEdge (axisF rel) (rel.w * rel.w - sOf rel * sOf rel) (2.0 * rel.w * sOf rel) qa
            (coneBody xs d k) (coneAxis xs d k) (coneCos xs d k) (coneKind xs d k)) :=
  rfl

/-- An accepted static check at the attitude `q` puts every cone's tube around the normalized
body vector on the allowed side. -/
theorem attitudeOk_sound {xs : Array Float} {d : Dims} {q : Q4} (hq : GoodQ q)
    (hcones : ∀ k : Nat, k < d.nc.toNat → ConeGood xs d (UInt64.ofNat k))
    (h : attitudeOk xs d q 0.0 = true) (k : Nat) (hk : k < d.nc.toNat) :
    PointSafe q (coneBody xs d (UInt64.ofNat k)) (coneAxis xs d (UInt64.ofNat k))
      (coneCos xs d (UInt64.ofNat k)) (coneKind xs d (UInt64.ofNat k)) := by
  obtain ⟨hb, hu, hc, hc1⟩ := hcones k hk
  rw [attitudeOk_eq] at h
  exact coneStatic_point hq hb hu hc hc1 (loop_all h k hk)

/-- An accepted edge check keeps every cone along the rotation `rel` from the attitude `qa`. -/
theorem edgeOk_sound {xs : Array Float} {d : Dims} {qa rel : Q4} (hq : GoodQ qa)
    (hr : GoodRel rel) (hcones : ∀ k : Nat, k < d.nc.toNat → ConeGood xs d (UInt64.ofNat k))
    (h : edgeOk xs d qa rel = true) (k : Nat) (hk : k < d.nc.toNat) :
    ArcSafe qa rel (coneBody xs d (UInt64.ofNat k)) (coneAxis xs d (UInt64.ofNat k))
      (coneCos xs d (UInt64.ofNat k)) (coneKind xs d (UInt64.ofNat k)) := by
  obtain ⟨hb, hu, hc, hc1⟩ := hcones k hk
  rw [edgeOk_eq] at h
  by_cases hs : sOf rel < sMin
  · rw [ite_eq_left hs] at h
    exact coneStatic_edge hq hb hu hc hc1 hr hs (loop_all h k hk)
  · rw [ite_eq_right hs] at h
    exact coneEdge_sound hq hb hu hc hc1 hr hs (loop_all h k hk)

end Demos.Slew.Check
