import Demos.Slew.Normalize
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Rotations as quaternion actions.  `act q v` is the vector part of `q v q*`, which for a unit
quaternion `q` equals the program's rotation formula `Quat.rot q v` (`rot_eq_act`).  The action
composes with the quaternion product (`act_qmul`), and for unit quaternions `p` and `p'` it moves
a vector `v` by at most `2 |p - p'| |v|` (`act_sub_le`), since the quaternion norm is
multiplicative and satisfies the triangle inequality.  Rodrigues' rotation by `φ` about a unit
axis `n` is the action of `(cos (φ/2), sin (φ/2) n)` (`rod_eq_act`), and the axis and angle of a
quaternion `r` with `w ≥ 0` give `r` normalized (`half_axis_angle`). -/

namespace Demos.Slew.Rotation

open Demos.Slew.Spec Demos.Slew.Arc Demos.Slew.Normalize Real

/-- The Hamilton product. -/
def qmul (p q : Quat) : Quat :=
  ⟨p.w * q.w - p.x * q.x - p.y * q.y - p.z * q.z, p.w * q.x + p.x * q.w + p.y * q.z - p.z * q.y,
    p.w * q.y - p.x * q.z + p.y * q.w + p.z * q.x, p.w * q.z + p.x * q.y - p.y * q.x + p.z * q.w⟩

def conj (q : Quat) : Quat := ⟨q.w, -q.x, -q.y, -q.z⟩

def qsub (p q : Quat) : Quat := ⟨p.w - q.w, p.x - q.x, p.y - q.y, p.z - q.z⟩

def qadd (p q : Quat) : Quat := ⟨p.w + q.w, p.x + q.x, p.y + q.y, p.z + q.z⟩

def qneg (q : Quat) : Quat := ⟨-q.w, -q.x, -q.y, -q.z⟩

def pure (v : Vec) : Quat := ⟨0, v.x, v.y, v.z⟩

def vpart (q : Quat) : Vec := ⟨q.x, q.y, q.z⟩

/-- The length of a quaternion. -/
noncomputable def qnorm (q : Quat) : ℝ := √(Quat.norm2 q)

/-- The action `v ↦ q v q*`. -/
def act (q : Quat) (v : Vec) : Vec := vpart (qmul (qmul q (pure v)) (conj q))

/-- The quaternion of the rotation by `φ` about the axis `n`. -/
noncomputable def half (n : Vec) (φ : ℝ) : Quat :=
  ⟨cos (φ / 2), sin (φ / 2) * n.x, sin (φ / 2) * n.y, sin (φ / 2) * n.z⟩

/-! ### Algebra -/

theorem norm2_nonneg (q : Quat) : 0 ≤ Quat.norm2 q := by
  simp only [Quat.norm2]
  nlinarith [mul_self_nonneg q.w, mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]

theorem rot_eq_act (q : Quat) (v : Vec) (h : Quat.norm2 q = 1) : Quat.rot q v = act q v := by
  simp only [Quat.norm2] at h
  ext
  · simp only [Quat.rot, act, vpart, qmul, conj, pure]; linear_combination (-v.x) * h
  · simp only [Quat.rot, act, vpart, qmul, conj, pure]; linear_combination (-v.y) * h
  · simp only [Quat.rot, act, vpart, qmul, conj, pure]; linear_combination (-v.z) * h

theorem act_qmul (p q : Quat) (v : Vec) : act (qmul p q) v = act p (act q v) := by
  ext <;> simp only [act, vpart, qmul, conj, pure] <;> ring

theorem act_qneg (q : Quat) (v : Vec) : act (qneg q) v = act q v := by
  ext <;> simp only [act, vpart, qmul, conj, pure, qneg] <;> ring

theorem norm2_qmul (p q : Quat) : Quat.norm2 (qmul p q) = Quat.norm2 p * Quat.norm2 q := by
  simp only [Quat.norm2, qmul]; ring

theorem norm2_conj (q : Quat) : Quat.norm2 (conj q) = Quat.norm2 q := by
  simp only [Quat.norm2, conj]; ring

theorem norm2_pure (v : Vec) : Quat.norm2 (pure v) = Vec.dot v v := by
  simp only [Quat.norm2, pure, Vec.dot]; ring

theorem qnorm_nonneg (q : Quat) : 0 ≤ qnorm q := Real.sqrt_nonneg _

theorem qnorm_qmul (p q : Quat) : qnorm (qmul p q) = qnorm p * qnorm q := by
  rw [qnorm, qnorm, qnorm, norm2_qmul, Real.sqrt_mul (norm2_nonneg p)]

theorem qnorm_conj (q : Quat) : qnorm (conj q) = qnorm q := by rw [qnorm, qnorm, norm2_conj]

theorem qnorm_pure (v : Vec) : qnorm (pure v) = Vec.norm v := by rw [qnorm, norm2_pure]; rfl

theorem qnorm_of_unit {q : Quat} (h : Quat.norm2 q = 1) : qnorm q = 1 := by
  rw [qnorm, h, Real.sqrt_one]

theorem qnorm_sq (q : Quat) : qnorm q * qnorm q = Quat.norm2 q :=
  Real.mul_self_sqrt (norm2_nonneg q)

theorem qnorm_qneg (q : Quat) : qnorm (qneg q) = qnorm q := by
  rw [qnorm, qnorm]; congr 1; simp only [Quat.norm2, qneg]; ring

/-- Cauchy–Schwarz for quaternions, by Lagrange's identity. -/
theorem qdot_le (p q : Quat) :
    p.w * q.w + p.x * q.x + p.y * q.y + p.z * q.z ≤ qnorm p * qnorm q := by
  rw [qnorm, qnorm, ← Real.sqrt_mul (norm2_nonneg p)]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  simp only [Quat.norm2]
  nlinarith [sq_nonneg (p.w * q.x - p.x * q.w), sq_nonneg (p.w * q.y - p.y * q.w),
    sq_nonneg (p.w * q.z - p.z * q.w), sq_nonneg (p.x * q.y - p.y * q.x),
    sq_nonneg (p.x * q.z - p.z * q.x), sq_nonneg (p.y * q.z - p.z * q.y)]

theorem qnorm_add_le (p q : Quat) : qnorm (qadd p q) ≤ qnorm p + qnorm q := by
  have hp := qnorm_nonneg p
  have hq := qnorm_nonneg q
  have hd := qdot_le p q
  have hp2 := qnorm_sq p
  have hq2 := qnorm_sq q
  rw [show qnorm p + qnorm q = √((qnorm p + qnorm q) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  simp only [Quat.norm2, qadd] at hp2 hq2 ⊢
  nlinarith

theorem qnorm_sub_comm (p q : Quat) : qnorm (qsub p q) = qnorm (qsub q p) := by
  rw [qnorm, qnorm]; congr 1; simp only [Quat.norm2, qsub]; ring

theorem qnorm_sub_triangle (a b c : Quat) :
    qnorm (qsub a c) ≤ qnorm (qsub a b) + qnorm (qsub b c) := by
  have e : qsub a c = qadd (qsub a b) (qsub b c) := by
    ext <;> simp only [qsub, qadd] <;> ring
  rw [e]; exact qnorm_add_le _ _

theorem norm_vpart_le (q : Quat) : Vec.norm (vpart q) ≤ qnorm q := by
  apply Real.sqrt_le_sqrt
  simp only [Vec.dot, vpart, Quat.norm2]
  nlinarith [mul_self_nonneg q.w]

theorem norm_sub_swap (a b : Vec) : Vec.norm (Vec.sub a b) = Vec.norm (Vec.sub b a) := by
  rw [Vec.norm, Vec.norm]; congr 1; simp only [Vec.dot, Vec.sub]; ring

/-! ### Distances between rotations -/

/-- Two unit quaternions move a vector `v` apart by at most twice their distance times `|v|`. -/
theorem act_sub_le (p p' : Quat) (v : Vec) (hp : Quat.norm2 p = 1) (hp' : Quat.norm2 p' = 1) :
    Vec.norm (Vec.sub (act p v) (act p' v)) ≤ 2 * qnorm (qsub p p') * Vec.norm v := by
  set d := qsub p p'
  have e : Vec.sub (act p v) (act p' v) =
      vpart (qadd (qmul (qmul d (pure v)) (conj p)) (qmul (qmul p' (pure v)) (conj d))) := by
    ext <;> simp only [Vec.sub, act, vpart, qadd, qmul, conj, pure, d, qsub] <;> ring
  rw [e]
  refine (norm_vpart_le _).trans ((qnorm_add_le _ _).trans ?_)
  rw [qnorm_qmul, qnorm_qmul, qnorm_qmul, qnorm_qmul, qnorm_conj, qnorm_conj, qnorm_pure,
    qnorm_of_unit hp, qnorm_of_unit hp']
  linarith

/-! ### Normalization and products -/

def one : Quat := ⟨1, 0, 0, 0⟩

theorem qmul_assoc (a b c : Quat) : qmul (qmul a b) c = qmul a (qmul b c) := by
  ext <;> simp only [qmul] <;> ring

theorem qmul_one (q : Quat) : qmul q one = q := by
  ext <;> simp only [qmul, one] <;> ring

theorem conj_qmul_self (q : Quat) (h : Quat.norm2 q = 1) : qmul (conj q) q = one := by
  simp only [Quat.norm2] at h
  ext
  · simp only [qmul, conj, one]; linear_combination h
  all_goals simp only [qmul, conj, one]; ring

theorem qsub_qmul_right (a b c : Quat) : qsub (qmul a c) (qmul b c) = qmul (qsub a b) c := by
  ext <;> simp only [qsub, qmul] <;> ring

theorem qnorm_smul (k : ℝ) (q : Quat) : qnorm (Quat.smul k q) = |k| * qnorm q := by
  rw [qnorm, qnorm, show Quat.norm2 (Quat.smul k q) = (k * k) * Quat.norm2 q by
    simp only [Quat.norm2, Quat.smul]; ring, Real.sqrt_mul (mul_self_nonneg k),
    Real.sqrt_mul_self_eq_abs]

theorem unit_eq (q : Quat) : Quat.unit q = Quat.smul (1 / qnorm q) q := rfl

theorem norm2_pos_of_qnorm {q : Quat} (h : 0 < qnorm q) : 0 < Quat.norm2 q := by
  have := qnorm_sq q; nlinarith

theorem qnorm_pos {q : Quat} (h : 0 < Quat.norm2 q) : 0 < qnorm q := Real.sqrt_pos.mpr h

theorem unit_qneg (q : Quat) : Quat.unit (qneg q) = qneg (Quat.unit q) := by
  rw [unit_eq, unit_eq, qnorm_qneg]
  ext <;> simp only [Quat.smul, qneg] <;> ring

theorem unit_conj (q : Quat) : Quat.unit (conj q) = conj (Quat.unit q) := by
  rw [unit_eq, unit_eq, qnorm_conj]
  ext <;> simp only [Quat.smul, conj] <;> ring

theorem unit_qmul (p q : Quat) : Quat.unit (qmul p q) = qmul (Quat.unit p) (Quat.unit q) := by
  rw [unit_eq, unit_eq, unit_eq, qnorm_qmul]
  ext <;> simp only [Quat.smul, qmul] <;> field_simp

/-- Normalization at most doubles a distance relative to the second length. -/
theorem unit_sub_le (a b : Quat) (hb : 0 < Quat.norm2 b) :
    qnorm (qsub (Quat.unit a) (Quat.unit b)) ≤ 2 * qnorm (qsub a b) / qnorm b := by
  have hnb := qnorm_pos hb
  have hab : |qnorm a - qnorm b| ≤ qnorm (qsub a b) := by
    have t1 : qnorm a ≤ qnorm (qsub a b) + qnorm b := by
      have e : a = qadd (qsub a b) b := by ext <;> simp only [qadd, qsub] <;> ring
      calc qnorm a = qnorm (qadd (qsub a b) b) := by rw [← e]
        _ ≤ _ := qnorm_add_le _ _
    have t2 : qnorm b ≤ qnorm (qsub a b) + qnorm a := by
      have e : b = qadd (qsub b a) a := by ext <;> simp only [qadd, qsub] <;> ring
      calc qnorm b = qnorm (qadd (qsub b a) a) := by rw [← e]
        _ ≤ qnorm (qsub b a) + qnorm a := qnorm_add_le _ _
        _ = qnorm (qsub a b) + qnorm a := by rw [qnorm_sub_comm]
    rw [abs_le]; constructor <;> linarith
  have hd0 := qnorm_nonneg (qsub a b)
  by_cases ha : qnorm a = 0
  · have hua : Quat.unit a = Quat.smul 0 a := by rw [unit_eq, ha, div_zero]
    have e : qsub (Quat.unit a) (Quat.unit b) = qneg (Quat.unit b) := by
      rw [hua]; ext <;> simp only [qsub, qneg, Quat.smul] <;> ring
    rw [e, qnorm_qneg, qnorm_of_unit (norm2_unit b hb), le_div_iff₀ hnb]
    rw [ha] at hab
    have : qnorm b ≤ qnorm (qsub a b) := by
      have := (abs_le.mp hab).1; linarith
    linarith
  · have hna : 0 < qnorm a := lt_of_le_of_ne (qnorm_nonneg a) (Ne.symm ha)
    have e : qsub (Quat.unit a) (Quat.unit b) =
        qadd (Quat.smul (1 / qnorm b) (qsub a b)) (Quat.smul (1 / qnorm a - 1 / qnorm b) a) := by
      rw [unit_eq, unit_eq]
      ext <;> simp only [qsub, qadd, Quat.smul] <;> ring
    rw [e]
    refine (qnorm_add_le _ _).trans ?_
    rw [qnorm_smul, qnorm_smul, abs_of_pos (by positivity : (0 : ℝ) < 1 / qnorm b)]
    have e2 : |1 / qnorm a - 1 / qnorm b| * qnorm a = |qnorm b - qnorm a| / qnorm b := by
      rw [show 1 / qnorm a - 1 / qnorm b = (qnorm b - qnorm a) / (qnorm a * qnorm b) by
        field_simp, abs_div, abs_of_pos (by positivity : (0 : ℝ) < qnorm a * qnorm b)]
      field_simp
    rw [e2, abs_sub_comm]
    have : |qnorm a - qnorm b| / qnorm b ≤ qnorm (qsub a b) / qnorm b :=
      div_le_div_of_nonneg_right hab hnb.le
    have e3 : 1 / qnorm b * qnorm (qsub a b) = qnorm (qsub a b) / qnorm b := by ring
    rw [e3]
    have e4 : 2 * qnorm (qsub a b) / qnorm b = qnorm (qsub a b) / qnorm b +
      qnorm (qsub a b) / qnorm b := by ring
    linarith

/-! ### Rodrigues' rotation -/

theorem rod_eq_act (n : Vec) (φ : ℝ) (v : Vec) (hn : Vec.dot n n = 1) :
    rod n φ v = act (half n φ) v := by
  have hc : cos φ = 2 * cos (φ / 2) ^ 2 - 1 := by
    rw [← cos_two_mul, show 2 * (φ / 2) = φ by ring]
  have hs : sin φ = 2 * sin (φ / 2) * cos (φ / 2) := by
    rw [← sin_two_mul, show 2 * (φ / 2) = φ by ring]
  have hp := sin_sq_add_cos_sq (φ / 2)
  simp only [Vec.dot] at hn
  simp only [rod, act, vpart, half, qmul, conj, pure, Vec.cross, Vec.dot]
  rw [hc, hs]
  set c := cos (φ / 2)
  set s := sin (φ / 2)
  ext
  · linear_combination (v.x - 2 * n.x * (n.x * v.x + n.y * v.y + n.z * v.z)) * hp +
      v.x * s ^ 2 * hn
  · linear_combination (v.y - 2 * n.y * (n.x * v.x + n.y * v.y + n.z * v.z)) * hp +
      v.y * s ^ 2 * hn
  · linear_combination (v.z - 2 * n.z * (n.x * v.x + n.y * v.y + n.z * v.z)) * hp +
      v.z * s ^ 2 * hn

theorem norm2_half (n : Vec) (φ : ℝ) (hn : Vec.dot n n = 1) : Quat.norm2 (half n φ) = 1 := by
  have hp := sin_sq_add_cos_sq (φ / 2)
  simp only [Vec.dot] at hn
  simp only [Quat.norm2, half]
  linear_combination hp + sin (φ / 2) ^ 2 * hn

/-- The distance between two rotation quaternions is at most the difference of the angles plus
the distance between the axes. -/
theorem qnorm_half_sub_le (n n' : Vec) (φ φ' : ℝ) (hn : Vec.dot n n = 1) :
    qnorm (qsub (half n φ) (half n' φ')) ≤ |φ - φ'| + Vec.norm (Vec.sub n n') := by
  have hc := Real.abs_cos_sub_cos_le (φ / 2) (φ' / 2)
  have hs := Real.abs_sin_sub_sin_le (φ / 2) (φ' / 2)
  have hs1 := abs_sin_le_one (φ' / 2)
  have hnn := norm_eq_one_of n hn
  set s := sin (φ / 2)
  set s' := sin (φ' / 2)
  set c := cos (φ / 2)
  set c' := cos (φ' / 2)
  have ev : Vec.sub (Vec.smul s n) (Vec.smul s' n') =
      Vec.sub (Vec.smul (s - s') n) (Vec.smul s' (Vec.sub n' n)) := by
    ext <;> simp only [Vec.sub, Vec.smul] <;> ring
  have hv : Vec.norm (Vec.sub (Vec.smul s n) (Vec.smul s' n')) ≤
      |φ / 2 - φ' / 2| + Vec.norm (Vec.sub n n') := by
    rw [ev]
    refine (norm_sub_le _ _).trans ?_
    rw [Arc.norm_smul, Arc.norm_smul, hnn, mul_one, norm_sub_swap n' n]
    have := Arc.norm_nonneg (Vec.sub n n')
    nlinarith [abs_nonneg s']
  have e : qsub (half n φ) (half n' φ') =
      qadd ⟨c - c', 0, 0, 0⟩ (pure (Vec.sub (Vec.smul s n) (Vec.smul s' n'))) := by
    ext <;> simp only [qsub, half, qadd, pure, Vec.sub, Vec.smul, c, c', s, s'] <;> ring
  rw [e]
  refine (qnorm_add_le _ _).trans ?_
  rw [qnorm_pure]
  have h1 : qnorm ⟨c - c', 0, 0, 0⟩ = |c - c'| := by
    rw [qnorm]; simp only [Quat.norm2]
    rw [show (c - c') * (c - c') + 0 * 0 + 0 * 0 + 0 * 0 = (c - c') ^ 2 by ring,
      Real.sqrt_sq_eq_abs]
  rw [h1]
  have : |φ / 2 - φ' / 2| = |φ - φ'| / 2 := by
    rw [show φ / 2 - φ' / 2 = (φ - φ') / 2 by ring, abs_div, abs_two]
  linarith

/-! ### Axis and angle -/

/-- For a quaternion `r` with `w ≥ 0` and a nonzero vector part of length `S`, the rotation
quaternion of the axis `r_v / S` and the angle `angle w S` is `r` normalized. -/
theorem half_axis_angle (r : Quat) (hw : 0 ≤ r.w)
    (hS : 0 < Vec.norm (vpart r)) :
    half (Vec.unit (vpart r)) (angle r.w (Vec.norm (vpart r))) = Quat.unit r := by
  set S := Vec.norm (vpart r)
  have hSS : S * S = r.x * r.x + r.y * r.y + r.z * r.z := by
    rw [norm_sq]; simp only [Vec.dot, vpart]
  have hQ : Quat.norm2 r = r.w * r.w + S * S := by rw [hSS]; simp only [Quat.norm2]; ring
  have hQpos : 0 < r.w * r.w + S * S := by nlinarith [mul_self_nonneg r.w]
  have hc := cos_angle r.w S hQpos
  have hθ0 := angle_nonneg r.w S
  have hθπ := angle_le_pi r.w S
  have hch : cos (angle r.w S / 2) = r.w / √(r.w * r.w + S * S) := by
    rw [Real.cos_half (by linarith [pi_pos]) hθπ, hc]
    rw [show (1 + (r.w * r.w - S * S) / (r.w * r.w + S * S)) / 2 =
      (r.w / √(r.w * r.w + S * S)) ^ 2 by
        rw [div_pow, Real.sq_sqrt hQpos.le]; field_simp; ring]
    exact Real.sqrt_sq (div_nonneg hw (Real.sqrt_nonneg _))
  have hsh : sin (angle r.w S / 2) = S / √(r.w * r.w + S * S) := by
    rw [Real.sin_half_eq_sqrt hθ0 (by linarith [pi_pos]), hc]
    rw [show (1 - (r.w * r.w - S * S) / (r.w * r.w + S * S)) / 2 =
      (S / √(r.w * r.w + S * S)) ^ 2 by
        rw [div_pow, Real.sq_sqrt hQpos.le]; field_simp; ring]
    exact Real.sqrt_sq (div_nonneg hS.le (Real.sqrt_nonneg _))
  have hQs : √(Quat.norm2 r) = √(r.w * r.w + S * S) := by rw [hQ]
  have hsq : 0 < √(r.w * r.w + S * S) := Real.sqrt_pos.mpr hQpos
  have ex : (vpart r).x = r.x := rfl
  have ey : (vpart r).y = r.y := rfl
  have ez : (vpart r).z = r.z := rfl
  have eS : Vec.norm (vpart r) = S := rfl
  ext <;>
    simp only [half, Quat.unit, Quat.smul, Vec.unit, Vec.smul, ex, ey, ez, eS, hch, hsh, hQs] <;>
    field_simp

/-- Rodrigues' rotation by the axis and angle of `r` is the action of `r` normalized. -/
theorem rod_axis_angle (r : Quat) (hw : 0 ≤ r.w) (hQ : 0 < Quat.norm2 r) (v : Vec) :
    rod (Vec.unit (vpart r)) (angle r.w (Vec.norm (vpart r))) v = act (Quat.unit r) v := by
  by_cases hS : Vec.norm (vpart r) = 0
  · have hv0 : r.x = 0 ∧ r.y = 0 ∧ r.z = 0 := by
      have h := norm_sq (vpart r)
      rw [hS] at h
      simp only [Vec.dot, vpart] at h
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_self_nonneg r.x, mul_self_nonneg r.y,
        mul_self_nonneg r.z]
    have hwpos : 0 < r.w := by
      simp only [Quat.norm2, hv0.1, hv0.2.1, hv0.2.2] at hQ
      rcases lt_or_eq_of_le hw with h | h
      · exact h
      · rw [← h] at hQ; norm_num at hQ
    have hrod : rod (Vec.unit (vpart r)) 0 v = v := by ext <;> simp [rod]
    have hang : angle r.w 0 = 0 := by
      unfold angle
      rw [show (r.w * r.w - 0 * 0) / (r.w * r.w + 0 * 0) = 1 by
        rw [mul_zero, sub_zero, add_zero, div_self (by positivity)], arccos_one]
    rw [hS, hang, hrod]
    have hN : Quat.norm2 r = r.w * r.w := by
      simp only [Quat.norm2, hv0.1, hv0.2.1, hv0.2.2]; ring
    have hsq : √(Quat.norm2 r) = r.w := by rw [hN, Real.sqrt_mul_self hw]
    have hne : r.w ≠ 0 := hwpos.ne'
    ext <;> simp only [act, vpart, qmul, conj, pure, Quat.unit, Quat.smul, hsq, hv0.1, hv0.2.1,
      hv0.2.2] <;> field_simp <;> ring
  · have hSpos : 0 < Vec.norm (vpart r) := lt_of_le_of_ne (Arc.norm_nonneg _) (Ne.symm hS)
    rw [rod_eq_act _ _ _ (by
      have := Arc.norm_unit _ hSpos
      rw [Vec.norm] at this
      have h0 := dot_self_nonneg (Vec.unit (vpart r))
      nlinarith [Real.sq_sqrt h0]), half_axis_angle r hw hSpos]

end Demos.Slew.Rotation
