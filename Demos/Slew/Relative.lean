import Demos.Slew.Check
import Demos.Slew.Rotation

/-! The relative quaternion of an edge.  For attitudes `qa` and `qb` whose squared norms lie
within `3e-12` of 1, each component of `relative qa qb` lies within `13.04 u` of the exact
product `qb qa*`, up to the common sign that makes `w ≥ 0` (`relative_cases`), so `relative qa qb`
satisfies `GoodRel` (`relative_good`).  The rotation of `rel`'s real value, applied after the
rotation of `qa`, then lies within `1.2e-14` of the rotation of `qb` (`relative_rot`), and
Rodrigues' rotation by the axis and angle of `rel`'s real value is the action of `rel`
normalized (`rod_rel`). -/

namespace Demos.Slew.Relative

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error Demos.Slew.Axis Demos.Slew.Cone
open Demos.Slew.Normalize Demos.Slew.Arc Demos.Slew.Decide Demos.Slew.Check Demos.Slew.Rotation
open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx

set_option exponentiation.threshold 4096

/-! ### The components -/

theorem quad_add {a1 a2 a3 a4 b1 b2 b3 b4 : Float}
    (h1 : Bnd a1 (val a1) 0 1.001) (h2 : Bnd a2 (val a2) 0 1.001) (h3 : Bnd a3 (val a3) 0 1.001)
    (h4 : Bnd a4 (val a4) 0 1.001) (k1 : Bnd b1 (val b1) 0 1.001) (k2 : Bnd b2 (val b2) 0 1.001)
    (k3 : Bnd b3 (val b3) 0 1.001) (k4 : Bnd b4 (val b4) 0 1.001) :
    Bnd (a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4)
      (val a1 * val b1 + val a2 * val b2 + val a3 * val b3 + val a4 * val b4) (13.04 / 2 ^ 53)
      4.01 := by
  have p1 := Bnd.mul (1.003 / 2 ^ 53) h1 k1 (by norm_num) (by norm_num)
  have p2 := Bnd.mul (1.003 / 2 ^ 53) h2 k2 (by norm_num) (by norm_num)
  have p3 := Bnd.mul (1.003 / 2 ^ 53) h3 k3 (by norm_num) (by norm_num)
  have p4 := Bnd.mul (1.003 / 2 ^ 53) h4 k4 (by norm_num) (by norm_num)
  have s2 := Bnd.add (4.011 / 2 ^ 53) p1 p2 (by norm_num) (by norm_num)
  have s3 := Bnd.add (8.021 / 2 ^ 53) s2 p3 (by norm_num) (by norm_num)
  have s4 := Bnd.add (13.04 / 2 ^ 53) s3 p4 (by norm_num) (by norm_num)
  exact s4.mono le_rfl (by norm_num)

theorem quad_sub {a1 a2 a3 a4 b1 b2 b3 b4 : Float}
    (h1 : Bnd a1 (val a1) 0 1.001) (h2 : Bnd a2 (val a2) 0 1.001) (h3 : Bnd a3 (val a3) 0 1.001)
    (h4 : Bnd a4 (val a4) 0 1.001) (k1 : Bnd b1 (val b1) 0 1.001) (k2 : Bnd b2 (val b2) 0 1.001)
    (k3 : Bnd b3 (val b3) 0 1.001) (k4 : Bnd b4 (val b4) 0 1.001) :
    Bnd (a1 * b1 - a2 * b2 - a3 * b3 + a4 * b4)
      (val a1 * val b1 - val a2 * val b2 - val a3 * val b3 + val a4 * val b4) (13.04 / 2 ^ 53)
      4.01 := by
  have p1 := Bnd.mul (1.003 / 2 ^ 53) h1 k1 (by norm_num) (by norm_num)
  have p2 := Bnd.mul (1.003 / 2 ^ 53) h2 k2 (by norm_num) (by norm_num)
  have p3 := Bnd.mul (1.003 / 2 ^ 53) h3 k3 (by norm_num) (by norm_num)
  have p4 := Bnd.mul (1.003 / 2 ^ 53) h4 k4 (by norm_num) (by norm_num)
  have s2 := Bnd.sub (4.011 / 2 ^ 53) p1 p2 (by norm_num) (by norm_num)
  have s3 := Bnd.sub (8.021 / 2 ^ 53) s2 p3 (by norm_num) (by norm_num)
  have s4 := Bnd.add (13.04 / 2 ^ 53) s3 p4 (by norm_num) (by norm_num)
  exact s4.mono le_rfl (by norm_num)

/-- The exact relative quaternion `qb qa*`. -/
noncomputable def exact (qa qb : Q4) : Quat := qmul (quatOf qb) (conj (quatOf qa))

/-- The four components of `relative qa qb` before the sign. -/
def relW (qa qb : Q4) : Float := qb.w * qa.w + qb.x * qa.x + qb.y * qa.y + qb.z * qa.z
def relX (qa qb : Q4) : Float := qb.x * qa.w - qb.w * qa.x - qb.y * qa.z + qb.z * qa.y
def relY (qa qb : Q4) : Float := qb.y * qa.w - qb.w * qa.y - qb.z * qa.x + qb.x * qa.z
def relZ (qa qb : Q4) : Float := qb.z * qa.w - qb.w * qa.z - qb.x * qa.y + qb.y * qa.x

theorem relative_eq (qa qb : Q4) :
    relative qa qb = if relW qa qb < 0.0 then ⟨-relW qa qb, -relX qa qb, -relY qa qb, -relZ qa qb⟩
      else ⟨relW qa qb, relX qa qb, relY qa qb, relZ qa qb⟩ := rfl

theorem quatOf_norm2_bounds {q : Q4} (h : GoodQ q) :
    1 - 3e-12 ≤ Quat.norm2 (quatOf q) ∧ Quat.norm2 (quatOf q) ≤ 1 + 3e-12 := by
  have := abs_le.mp h.norm; constructor <;> linarith

theorem norm2_exact {qa qb : Q4} (ha : GoodQ qa) (hb : GoodQ qb) :
    |Quat.norm2 (exact qa qb) - 1| ≤ 6.01e-12 := by
  rw [exact, norm2_qmul, norm2_conj]
  have a := quatOf_norm2_bounds ha
  have b := quatOf_norm2_bounds hb
  rw [abs_le]; constructor <;> nlinarith

theorem abs_le_qnorm (q : Quat) :
    |q.w| ≤ qnorm q ∧ |q.x| ≤ qnorm q ∧ |q.y| ≤ qnorm q ∧ |q.z| ≤ qnorm q := by
  refine ⟨Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_⟩ <;>
    simp only [Quat.norm2, sq] <;>
    nlinarith [mul_self_nonneg q.w, mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]

theorem qnorm_exact_le {qa qb : Q4} (ha : GoodQ qa) (hb : GoodQ qb) :
    qnorm (exact qa qb) ≤ 1.0001 := by
  have h := norm2_exact ha hb
  rw [qnorm, show (1.0001 : ℝ) = √(1.0001 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith [(abs_le.mp h).2])

theorem qnorm_exact_ge {qa qb : Q4} (ha : GoodQ qa) (hb : GoodQ qb) :
    0.99999 ≤ qnorm (exact qa qb) := by
  have h := norm2_exact ha hb
  rw [qnorm, show (0.99999 : ℝ) = √(0.99999 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith [(abs_le.mp h).1])

/-- The components of `relative` before the sign, against the exact relative quaternion. -/
theorem rel_values {qa qb : Q4} (ha : GoodQ qa) (hb : GoodQ qb) :
    Bnd (relW qa qb) (exact qa qb).w (13.04 / 2 ^ 53) 1.0001 ∧
    Bnd (relX qa qb) (exact qa qb).x (13.04 / 2 ^ 53) 1.0001 ∧
    Bnd (relY qa qb) (exact qa qb).y (13.04 / 2 ^ 53) 1.0001 ∧
    Bnd (relZ qa qb) (exact qa qb).z (13.04 / 2 ^ 53) 1.0001 := by
  obtain ⟨aw, ax, ay, az⟩ := ha.components
  obtain ⟨bw, bx, byy, bz⟩ := hb.components
  obtain ⟨ew, ex, ey, ez⟩ := abs_le_qnorm (exact qa qb)
  have hn := qnorm_exact_le ha hb
  have w := quad_add bw bx byy bz aw ax ay az
  have x := quad_sub bx bw byy bz aw ax az ay
  have y := quad_sub byy bw bz bx aw ay ax az
  have z := quad_sub bz bw bx byy aw az ay ax
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (exact qa qb).w = val qb.w * val qa.w + val qb.x * val qa.x + val qb.y * val qa.y +
        val qb.z * val qa.z := by simp only [exact, qmul, conj, quatOf]; ring
    rw [e] at ew ⊢; exact w.rebound (ew.trans hn)
  · have e : (exact qa qb).x = val qb.x * val qa.w - val qb.w * val qa.x - val qb.y * val qa.z +
        val qb.z * val qa.y := by simp only [exact, qmul, conj, quatOf]; ring
    rw [e] at ex ⊢; exact x.rebound (ex.trans hn)
  · have e : (exact qa qb).y = val qb.y * val qa.w - val qb.w * val qa.y - val qb.z * val qa.x +
        val qb.x * val qa.z := by simp only [exact, qmul, conj, quatOf]; ring
    rw [e] at ey ⊢; exact y.rebound (ey.trans hn)
  · have e : (exact qa qb).z = val qb.z * val qa.w - val qb.w * val qa.z - val qb.x * val qa.y +
        val qb.y * val qa.x := by simp only [exact, qmul, conj, quatOf]; ring
    rw [e] at ez ⊢; exact z.rebound (ez.trans hn)

/-- The real values of the components before the sign. -/
noncomputable def raw (qa qb : Q4) : Quat :=
  ⟨val (relW qa qb), val (relX qa qb), val (relY qa qb), val (relZ qa qb)⟩

theorem raw_close {qa qb : Q4} (ha : GoodQ qa) (hb : GoodQ qb) :
    qnorm (qsub (raw qa qb) (exact qa qb)) ≤ 26.08 / 2 ^ 53 := by
  obtain ⟨w, x, y, z⟩ := rel_values ha hb
  have dw : |val (relW qa qb) - (exact qa qb).w| ≤ 13.04 / 2 ^ 53 := w.1.2
  have dx : |val (relX qa qb) - (exact qa qb).x| ≤ 13.04 / 2 ^ 53 := x.1.2
  have dy : |val (relY qa qb) - (exact qa qb).y| ≤ 13.04 / 2 ^ 53 := y.1.2
  have dz : |val (relZ qa qb) - (exact qa qb).z| ≤ 13.04 / 2 ^ 53 := z.1.2
  rw [qnorm, show (26.08 : ℝ) / 2 ^ 53 = √((26.08 / 2 ^ 53) ^ 2) by
    rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  simp only [Quat.norm2, qsub, raw]
  have sq : ∀ t : ℝ, |t| ≤ 13.04 / 2 ^ 53 → t * t ≤ (13.04 / 2 ^ 53) ^ 2 := by
    intro t ht; rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  have := sq _ dw
  have := sq _ dx
  have := sq _ dy
  have := sq _ dz
  nlinarith

/-- `relative qa qb` is the raw quaternion or its negation, by the sign of `w`. -/
theorem relative_cases {qa qb : Q4} (ha : GoodQ qa) (hb : GoodQ qb) :
    (quatOf (relative qa qb) = raw qa qb ∧ 0 ≤ val (relW qa qb)) ∨
      (quatOf (relative qa qb) = qneg (raw qa qb) ∧ val (relW qa qb) < 0) := by
  obtain ⟨w, x, y, z⟩ := rel_values ha hb
  rw [relative_eq]
  by_cases hneg : relW qa qb < 0.0
  · right
    rw [ite_eq_left hneg]
    have hv := lt_val_of_lt hneg
    rw [zero_val.2] at hv
    refine ⟨?_, hv⟩
    simp only [quatOf, raw, qneg]
    rw [(neg_val w.1.1).2, (neg_val x.1.1).2, (neg_val y.1.1).2, (neg_val z.1.1).2]
  · left
    rw [ite_eq_right hneg]
    refine ⟨rfl, ?_⟩
    rw [lt_iff_val w.1.1 zero_val.1, zero_val.2] at hneg
    linarith

/-- `relative qa qb` satisfies the hypotheses of the edge check. -/
theorem relative_good {qa qb : Q4} (ha : GoodQ qa) (hb : GoodQ qb) : GoodRel (relative qa qb) := by
  obtain ⟨w, x, y, z⟩ := rel_values ha hb
  have hN := norm2_exact ha hb
  have sqc : ∀ {f : Float} {P : ℝ}, Bnd f P (13.04 / 2 ^ 53) 1.0001 →
      |val f * val f - P * P| ≤ 13.04 / 2 ^ 53 * 2.0004 := by
    intro f P h
    have hd : |val f - P| ≤ 13.04 / 2 ^ 53 := h.1.2
    have hP := h.2
    rw [show val f * val f - P * P = (val f - P) * (val f + P) by ring, abs_mul]
    have : |val f + P| ≤ 2.0004 := by
      rw [show val f + P = (val f - P) + 2 * P by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      have : (13.04 : ℝ) / 2 ^ 53 ≤ 0.0002 := by norm_num
      linarith
    exact mul_le_mul hd this (abs_nonneg _) (by norm_num)
  have cw := sqc w
  have cx := sqc x
  have cy := sqc y
  have cz := sqc z
  have key : |val (relW qa qb) * val (relW qa qb) + (val (relX qa qb) * val (relX qa qb) +
      val (relY qa qb) * val (relY qa qb) + val (relZ qa qb) * val (relZ qa qb)) - 1| ≤ 1e-11 := by
    have e : Quat.norm2 (exact qa qb) = (exact qa qb).w * (exact qa qb).w +
        ((exact qa qb).x * (exact qa qb).x + (exact qa qb).y * (exact qa qb).y +
          (exact qa qb).z * (exact qa qb).z) := by simp only [Quat.norm2]; ring
    rw [e] at hN
    rw [abs_le] at cw cx cy cz hN ⊢
    constructor <;> linarith [cw.1, cw.2, cx.1, cx.2, cy.1, cy.2, cz.1, cz.2, hN.1, hN.2]
  rw [relative_eq]
  by_cases hneg : relW qa qb < 0.0
  · rw [ite_eq_left hneg]
    have hv := lt_val_of_lt hneg
    rw [zero_val.2] at hv
    obtain ⟨fw, vw⟩ := neg_val w.1.1
    obtain ⟨fx, vx⟩ := neg_val x.1.1
    obtain ⟨fy, vy⟩ := neg_val y.1.1
    obtain ⟨fz, vz⟩ := neg_val z.1.1
    refine ⟨fw, fx, fy, fz, ?_, ?_⟩
    · show 0 ≤ val (-relW qa qb); rw [vw]; linarith
    · show |val (-relW qa qb) * val (-relW qa qb) + s2 ⟨_, -relX qa qb, -relY qa qb, -relZ qa qb⟩
        - 1| ≤ 1e-11
      simp only [s2]
      rw [vw, vx, vy, vz]
      convert key using 2; ring
  · rw [ite_eq_right hneg]
    refine ⟨w.1.1, x.1.1, y.1.1, z.1.1, ?_, key⟩
    rw [lt_iff_val w.1.1 zero_val.1, zero_val.2] at hneg
    show 0 ≤ val (relW qa qb)
    linarith

/-! ### The rotation -/

theorem qnorm_quatOf_pos {q : Q4} (h : GoodQ q) : 0 < Quat.norm2 (quatOf q) := by
  have := quatOf_norm2_bounds h; linarith [this.1]

/-- The rotation of `rel`'s real value after the rotation of `qa` lies within `1.2e-14 |v|` of
the rotation of `qb`. -/
theorem relative_rot {qa qb : Q4} (ha : GoodQ qa) (hb : GoodQ qb) (v : Vec) :
    Vec.norm (Vec.sub (act (Quat.unit (quatOf (relative qa qb))) (act (Quat.unit (quatOf qa)) v))
      (act (Quat.unit (quatOf qb)) v)) ≤ 1.2e-14 * Vec.norm v := by
  have hA := qnorm_quatOf_pos ha
  have hB := qnorm_quatOf_pos hb
  have hEpos : 0 < Quat.norm2 (exact qa qb) := by
    have := norm2_exact ha hb; linarith [(abs_le.mp this).1]
  have hraw : act (Quat.unit (quatOf (relative qa qb))) = act (Quat.unit (raw qa qb)) := by
    funext u
    rcases relative_cases ha hb with ⟨e, _⟩ | ⟨e, _⟩
    · rw [e]
    · rw [e, unit_qneg, act_qneg]
  rw [hraw, ← act_qmul]
  set uA := Quat.unit (quatOf qa)
  set uB := Quat.unit (quatOf qb)
  have huA := norm2_unit _ hA
  have huB := norm2_unit _ hB
  have hE : qmul (Quat.unit (exact qa qb)) uA = uB := by
    rw [exact, unit_qmul, unit_conj, qmul_assoc, conj_qmul_self _ huA, qmul_one]
  have hR : 0 < Quat.norm2 (raw qa qb) := by
    have hc := raw_close ha hb
    have hl := qnorm_exact_ge ha hb
    have t : qnorm (exact qa qb) ≤ qnorm (qsub (exact qa qb) (raw qa qb)) + qnorm (raw qa qb) := by
      have e : exact qa qb = qadd (qsub (exact qa qb) (raw qa qb)) (raw qa qb) := by
        ext <;> simp only [qadd, qsub] <;> ring
      calc qnorm (exact qa qb) = qnorm (qadd (qsub (exact qa qb) (raw qa qb)) (raw qa qb)) := by
            rw [← e]
        _ ≤ _ := qnorm_add_le _ _
    rw [qnorm_sub_comm] at t
    have : 0 < qnorm (raw qa qb) := by
      have : (26.08 : ℝ) / 2 ^ 53 < 0.5 := by norm_num
      linarith
    exact norm2_pos_of_qnorm this
  have hRu := norm2_unit _ hR
  have hd := act_sub_le (qmul (Quat.unit (raw qa qb)) uA) uB v
    (by rw [norm2_qmul, hRu, huA, one_mul]) huB
  refine hd.trans ?_
  rw [← hE, qsub_qmul_right, qnorm_qmul, qnorm_of_unit huA, mul_one]
  have hu := unit_sub_le (raw qa qb) (exact qa qb) hEpos
  have hc := raw_close ha hb
  have hl := qnorm_exact_ge ha hb
  have hv := Arc.norm_nonneg v
  have h1 : qnorm (qsub (Quat.unit (raw qa qb)) (Quat.unit (exact qa qb))) ≤ 5.8e-15 := by
    refine hu.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : (26.08 : ℝ) / 2 ^ 53 * 2 ≤ 5.8e-15 * 0.99999 := by norm_num
    nlinarith
  nlinarith [qnorm_nonneg (qsub (Quat.unit (raw qa qb)) (Quat.unit (exact qa qb)))]

/-! ### Axis and angle -/

theorem vpart_quatOf (q : Q4) : vpart (quatOf q) = vecPart q := rfl

theorem norm_vpart_quatOf (q : Q4) : Vec.norm (vpart (quatOf q)) = √(s2 q) := rfl

/-- Rodrigues' rotation by the axis and angle of `rel`'s real value is the action of `rel`
normalized. -/
theorem rod_rel {rel : Q4} (h : GoodRel rel) (v : Vec) :
    rod (axisR rel) (angleR rel) v = act (Quat.unit (quatOf rel)) v := by
  have hQ : 0 < Quat.norm2 (quatOf rel) := by
    have := h.q_pos; simp only [s2] at this; simp only [Quat.norm2, quatOf]; linarith
  exact rod_axis_angle (quatOf rel) h.w_nonneg hQ v

end Demos.Slew.Relative
