import Demos.Attitude.Bound

/-! Davenport's matrix of Wahba's problem.  A quaternion is a vector of `ℝ⁴` with the inner product
`qdot`, and `Sym4` is a symmetric 4×4 matrix of reals by its entries on and above the diagonal.
`obsK b r` is Davenport's matrix of one observation with measurement `b` and reference `r`, whose
quadratic form at `q` is `r · act q b` (`form_obsK`), and `davK o n` is the weighted sum over the
first `n` observations of `o`, with normalized vectors.  `wahba_eq` states Davenport's reduction:
for a unit `q`, Wahba's loss is the sum of the weights less `qᵀ K q`.  `apply_apply_obsK` states
`K_i² = |b|² |r|² I`, from which `resid_obsK` gives the residual of a unit quaternion for one
observation of unit vectors, and `true_form` and `true_resid` bound the Rayleigh quotient and the
residual of a true attitude by the observations' error bounds. -/

namespace Demos.Attitude

open Demos.Slew.Spec Demos.Slew.Arc Demos.Slew.Normalize Demos.Slew.Rotation Demos.Slew.Safety
open Demos.Slew.Premise Vec Real

/-- The inner product of two quaternions as vectors of `ℝ⁴`. -/
def qdot (p q : Quat) : ℝ := p.w * q.w + p.x * q.x + p.y * q.y + p.z * q.z

theorem qdot_comm (p q : Quat) : qdot p q = qdot q p := by simp only [qdot]; ring

theorem qdot_self (q : Quat) : qdot q q = Quat.norm2 q := rfl

/-- The Cauchy–Schwarz inequality for `qdot`, by Lagrange's identity. -/
theorem qdot_sq_le (p q : Quat) : qdot p q ^ 2 ≤ Quat.norm2 p * Quat.norm2 q := by
  simp only [qdot, Quat.norm2]
  nlinarith [sq_nonneg (p.w * q.x - p.x * q.w), sq_nonneg (p.w * q.y - p.y * q.w),
    sq_nonneg (p.w * q.z - p.z * q.w), sq_nonneg (p.x * q.y - p.y * q.x),
    sq_nonneg (p.x * q.z - p.z * q.x), sq_nonneg (p.y * q.z - p.z * q.y)]

theorem norm2_smul (k : ℝ) (q : Quat) : Quat.norm2 (Quat.smul k q) = k ^ 2 * Quat.norm2 q := by
  simp only [Quat.norm2, Quat.smul]; ring

/-- A symmetric 4×4 matrix of reals by its entries on and above the diagonal, with the
quaternion's components in the order `w`, `x`, `y`, `z`. -/
structure Sym4 where
  a00 : ℝ
  a01 : ℝ
  a02 : ℝ
  a03 : ℝ
  a11 : ℝ
  a12 : ℝ
  a13 : ℝ
  a22 : ℝ
  a23 : ℝ
  a33 : ℝ

namespace Sym4

/-- The product `A q`. -/
def apply (A : Sym4) (q : Quat) : Quat :=
  ⟨A.a00 * q.w + A.a01 * q.x + A.a02 * q.y + A.a03 * q.z,
    A.a01 * q.w + A.a11 * q.x + A.a12 * q.y + A.a13 * q.z,
    A.a02 * q.w + A.a12 * q.x + A.a22 * q.y + A.a23 * q.z,
    A.a03 * q.w + A.a13 * q.x + A.a23 * q.y + A.a33 * q.z⟩

/-- The quadratic form `qᵀ A q`. -/
def form (A : Sym4) (q : Quat) : ℝ := qdot q (A.apply q)

def zero : Sym4 := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def add (A B : Sym4) : Sym4 :=
  ⟨A.a00 + B.a00, A.a01 + B.a01, A.a02 + B.a02, A.a03 + B.a03, A.a11 + B.a11, A.a12 + B.a12,
    A.a13 + B.a13, A.a22 + B.a22, A.a23 + B.a23, A.a33 + B.a33⟩

def smul (k : ℝ) (A : Sym4) : Sym4 :=
  ⟨k * A.a00, k * A.a01, k * A.a02, k * A.a03, k * A.a11, k * A.a12, k * A.a13, k * A.a22,
    k * A.a23, k * A.a33⟩

/-- `A - c I`. -/
def shift (A : Sym4) (c : ℝ) : Sym4 :=
  ⟨A.a00 - c, A.a01, A.a02, A.a03, A.a11 - c, A.a12, A.a13, A.a22 - c, A.a23, A.a33 - c⟩

/-- The residual `A q - (qᵀ A q) q`. -/
def resid (A : Sym4) (q : Quat) : Quat := qsub (A.apply q) (Quat.smul (A.form q) q)

theorem qdot_apply (A : Sym4) (p q : Quat) : qdot p (A.apply q) = qdot (A.apply p) q := by
  simp only [qdot, apply]; ring

theorem form_zero (q : Quat) : zero.form q = 0 := by simp only [form, qdot, apply, zero]; ring

theorem form_add (A B : Sym4) (q : Quat) : (A.add B).form q = A.form q + B.form q := by
  simp only [form, qdot, apply, add]; ring

theorem form_smul (k : ℝ) (A : Sym4) (q : Quat) : (smul k A).form q = k * A.form q := by
  simp only [form, qdot, apply, smul]; ring

theorem form_shift (A : Sym4) (c : ℝ) (q : Quat) :
    (A.shift c).form q = A.form q - c * Quat.norm2 q := by
  simp only [form, qdot, apply, shift, Quat.norm2]; ring

theorem form_qsmul (A : Sym4) (k : ℝ) (q : Quat) :
    A.form (Quat.smul k q) = k ^ 2 * A.form q := by
  simp only [form, qdot, apply, Quat.smul]; ring

theorem apply_shift (A : Sym4) (c : ℝ) (q : Quat) :
    (A.shift c).apply q = qsub (A.apply q) (Quat.smul c q) := by
  ext <;> simp only [apply, shift, qsub, Quat.smul] <;> ring

theorem resid_add (A B : Sym4) (q : Quat) : (A.add B).resid q = qadd (A.resid q) (B.resid q) := by
  have h := form_add A B q
  simp only [resid] at h ⊢
  rw [h]
  ext <;> simp only [apply, add, qsub, qadd, Quat.smul] <;> ring

theorem resid_smul (k : ℝ) (A : Sym4) (q : Quat) :
    (smul k A).resid q = Quat.smul k (A.resid q) := by
  have h := form_smul k A q
  simp only [resid] at h ⊢
  rw [h]
  ext <;> simp only [apply, smul, qsub, Quat.smul] <;> ring

end Sym4

/-! ### One observation -/

/-- Davenport's matrix of one observation with measurement `b` and reference `r`:
`[[r · b, (b × r)ᵀ], [b × r, r bᵀ + b rᵀ - (r · b) I]]`. -/
def obsK (b r : Vec) : Sym4 :=
  ⟨dot r b, (cross b r).x, (cross b r).y, (cross b r).z, 2 * (r.x * b.x) - dot r b,
    r.x * b.y + r.y * b.x, r.x * b.z + r.z * b.x, 2 * (r.y * b.y) - dot r b,
    r.y * b.z + r.z * b.y, 2 * (r.z * b.z) - dot r b⟩

/-- **Davenport's identity** for one observation: `qᵀ K q = r · (q b q*)`. -/
theorem form_obsK (b r : Vec) (q : Quat) : (obsK b r).form q = dot r (act q b) := by
  simp only [Sym4.form, qdot, Sym4.apply, obsK, dot, cross, act, vpart, qmul, conj,
    Demos.Slew.Rotation.pure]
  ring

/-- `K² = |b|² |r|² I` for the matrix of one observation. -/
theorem apply_apply_obsK (b r : Vec) (q : Quat) :
    (obsK b r).apply ((obsK b r).apply q) = Quat.smul (dot b b * dot r r) q := by
  ext <;> simp only [Sym4.apply, obsK, dot, cross, Quat.smul] <;> ring

/-- **Q3a.**  For unit `b`, `r`, and `q`, the residual of `q` for one observation has squared
length `1 - c²`, where `c = qᵀ K q` is the cosine of the angle between `R(q) b` and `r`. -/
theorem resid_obsK {b r : Vec} (hb : dot b b = 1) (hr : dot r r = 1) {q : Quat}
    (hq : Quat.norm2 q = 1) :
    Quat.norm2 ((obsK b r).resid q) = 1 - (obsK b r).form q ^ 2 := by
  set K := obsK b r
  have h2 : qdot (K.apply q) (K.apply q) = 1 := by
    rw [← Sym4.qdot_apply, apply_apply_obsK, hb, hr, one_mul]
    simp only [qdot, Quat.smul, Quat.norm2] at hq ⊢
    linear_combination hq
  have e : Quat.norm2 (K.resid q) = qdot (K.apply q) (K.apply q) -
      2 * K.form q * qdot q (K.apply q) + K.form q ^ 2 * Quat.norm2 q := by
    simp only [Sym4.resid, Quat.norm2, qdot, qsub, Quat.smul]; ring
  rw [e, h2, hq, ← Sym4.form]
  ring

/-! ### Observations and Davenport's matrix -/

/-- An observation: a measurement `b` in the body frame, a reference `r` in the inertial frame, a
weight `a`, and an error bound `ε`. -/
structure Obs where
  b : Vec
  r : Vec
  a : ℝ
  ε : ℝ

/-- The term `a K(b̄, r̄)` of an observation in Davenport's matrix. -/
noncomputable def Obs.K (o : Obs) : Sym4 := Sym4.smul o.a (obsK (unit o.b) (unit o.r))

/-- Davenport's matrix of the first `n` observations of `o`. -/
noncomputable def davK (o : ℕ → Obs) : ℕ → Sym4
  | 0 => Sym4.zero
  | n + 1 => (davK o n).add (o n).K

/-- Wahba's loss of the attitude of `q` over the first `n` observations:
`½ Σ a_i |r̄_i - R(q) b̄_i|²`. -/
noncomputable def wahba (o : ℕ → Obs) (n : ℕ) (q : Quat) : ℝ :=
  ∑ i ∈ Finset.range n, (o i).a / 2 *
    dot (sub (unit (o i).r) (attitude q (unit (o i).b)))
      (sub (unit (o i).r) (attitude q (unit (o i).b)))

/-- The quadratic form of Davenport's matrix is the weighted sum of the observations' forms. -/
theorem form_davK (o : ℕ → Obs) (n : ℕ) (q : Quat) :
    (davK o n).form q = ∑ i ∈ Finset.range n, (o i).a * (obsK (unit (o i).b) (unit (o i).r)).form q := by
  induction n with
  | zero => simp [davK, Sym4.form_zero]
  | succ n ih => rw [davK, Sym4.form_add, ih, Finset.sum_range_succ, Obs.K, Sym4.form_smul]

theorem unit_of_norm2_one {q : Quat} (hq : Quat.norm2 q = 1) : Quat.unit q = q := by
  ext <;> simp [Quat.unit, Quat.smul, hq]

theorem attitude_of_unit {q : Quat} (hq : Quat.norm2 q = 1) (v : Vec) : attitude q v = act q v := by
  rw [attitude_eq (by rw [hq]; norm_num), unit_of_norm2_one hq]

/-- **Q1, Davenport's reduction.**  For a unit `q` and observations with nonzero vectors, Wahba's
loss equals the sum of the weights less `qᵀ K q`. -/
theorem wahba_eq {o : ℕ → Obs} {n : ℕ} (hb : ∀ i < n, 0 < norm (o i).b)
    (hr : ∀ i < n, 0 < norm (o i).r) {q : Quat} (hq : Quat.norm2 q = 1) :
    wahba o n q = ∑ i ∈ Finset.range n, (o i).a - (davK o n).form q := by
  rw [form_davK, wahba, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hbb := dot_unit_self (hb i hi')
  have hrr := dot_unit_self (hr i hi')
  have hab : dot (act q (unit (o i).b)) (act q (unit (o i).b)) = 1 := by
    rw [dot_act, hq, hbb]; ring
  rw [form_obsK, attitude_of_unit hq]
  have e : ∀ u v : Vec, dot (sub u v) (sub u v) = dot u u - 2 * dot u v + dot v v := by
    intro u v; simp only [dot, sub]; ring
  rw [e, hrr, hab]
  ring

/-! ### The true attitude -/

/-- The cosine of the angle between `R(q) b̄` and `r̄` bounds by the error bound. -/
theorem cos_le_form {b r : Vec} (hb : 0 < norm b) (hr : 0 < norm r) {q : Quat}
    (hq : Quat.norm2 q = 1) {ε : ℝ} (hε : ε ≤ π) (h : vangle (attitude q (unit b)) (unit r) ≤ ε) :
    cos ε ≤ (obsK (unit b) (unit r)).form q := by
  rw [form_obsK, dot_comm, ← attitude_of_unit hq]
  have hu : dot (attitude q (unit b)) (attitude q (unit b)) = 1 := by
    rw [attitude_of_unit hq, dot_act, hq, dot_unit_self hb]; ring
  exact cos_le_dot hu (dot_unit_self hr) hε h

/-- The Rayleigh quotient of a true attitude is at least `Σ a_i cos ε_i`. -/
theorem true_form {o : ℕ → Obs} {n : ℕ} (hb : ∀ i < n, 0 < norm (o i).b)
    (hr : ∀ i < n, 0 < norm (o i).r) (ha : ∀ i < n, 0 ≤ (o i).a) (hε : ∀ i < n, (o i).ε ≤ π)
    {q : Quat} (hq : Quat.norm2 q = 1)
    (h : ∀ i < n, vangle (attitude q (unit (o i).b)) (unit (o i).r) ≤ (o i).ε) :
    ∑ i ∈ Finset.range n, (o i).a * cos (o i).ε ≤ (davK o n).form q := by
  rw [form_davK]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  exact mul_le_mul_of_nonneg_left (cos_le_form (hb i hi') (hr i hi') hq (hε i hi') (h i hi'))
    (ha i hi')

/-- The residual of a true attitude is at most `Σ a_i sin ε_i`, for error bounds in `[0, π/2]`. -/
theorem true_resid {o : ℕ → Obs} {n : ℕ} (hb : ∀ i < n, 0 < norm (o i).b)
    (hr : ∀ i < n, 0 < norm (o i).r) (ha : ∀ i < n, 0 ≤ (o i).a) (hε0 : ∀ i < n, 0 ≤ (o i).ε)
    (hε : ∀ i < n, (o i).ε ≤ π / 2) {q : Quat} (hq : Quat.norm2 q = 1)
    (h : ∀ i < n, vangle (attitude q (unit (o i).b)) (unit (o i).r) ≤ (o i).ε) :
    qnorm ((davK o n).resid q) ≤ ∑ i ∈ Finset.range n, (o i).a * sin (o i).ε := by
  induction n with
  | zero =>
    have e : (davK o 0).resid q = ⟨0, 0, 0, 0⟩ := by
      rw [show davK o 0 = Sym4.zero from rfl, Sym4.resid, Sym4.form_zero]
      ext <;> simp [Sym4.apply, Sym4.zero, qsub, Quat.smul]
    rw [e, Finset.sum_range_zero]
    simp [qnorm, Quat.norm2]
  | succ n ih =>
    have lt : n < n + 1 := Nat.lt_succ_self n
    have ih' := ih (fun i hi => hb i (by omega)) (fun i hi => hr i (by omega))
      (fun i hi => ha i (by omega)) (fun i hi => hε0 i (by omega)) (fun i hi => hε i (by omega))
      (fun i hi => h i (by omega))
    rw [davK, Sym4.resid_add, Finset.sum_range_succ, Obs.K, Sym4.resid_smul]
    refine (qnorm_add_le _ _).trans (add_le_add ih' ?_)
    rw [qnorm_smul, abs_of_nonneg (ha n lt)]
    refine mul_le_mul_of_nonneg_left ?_ (ha n lt)
    have hbb := dot_unit_self (hb n lt)
    have hrr := dot_unit_self (hr n lt)
    have hc := cos_le_form (hb n lt) (hr n lt) hq (by linarith [pi_pos, hε n lt]) (h n lt)
    have hc0 : 0 ≤ cos (o n).ε := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, hε0 n lt], hε n lt⟩
    have hs0 : 0 ≤ sin (o n).ε :=
      sin_nonneg_of_nonneg_of_le_pi (hε0 n lt) (by linarith [pi_pos, hε n lt])
    have hc1 : (obsK (unit (o n).b) (unit (o n).r)).form q ≤ 1 := by
      have := resid_obsK hbb hrr hq
      have := norm2_nonneg ((obsK (unit (o n).b) (unit (o n).r)).resid q)
      nlinarith
    rw [qnorm, resid_obsK hbb hrr hq]
    calc √(1 - (obsK (unit (o n).b) (unit (o n).r)).form q ^ 2) ≤ √(sin (o n).ε ^ 2) := by
          apply Real.sqrt_le_sqrt
          have := sin_sq_add_cos_sq (o n).ε
          nlinarith
      _ = sin (o n).ε := Real.sqrt_sq hs0

end Demos.Attitude
