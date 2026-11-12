import Demos.Attitude.Inertia

/-! The maximizer of Davenport's form and the bounds of the q-method.  `IsMax K e` states that the
unit quaternion `e` maximizes `qᵀ K q` on the unit sphere; one exists by compactness
(`exists_isMax`), and it is an eigenvector for the largest value `λ1 = eᵀ K e`
(`IsMax.apply_eq`), by a perturbation of `e` in a perpendicular direction.

`inertia_cut` (Q2) turns the inertia certificate of `K - c I` into a cut: `c < λ1`, and every unit
`q ⊥ e` has `qᵀ K q < c`.  The plane of `e` and such a `q` would meet the certificate's hyperplane
in a nonzero vector at which the form of `K - c I` is not negative.  `isMax_unique` derives that the
maximizer is unique up to sign.  `davis_kahan` (Q3) bounds the component perpendicular to `e` of a
unit vector by its residual over `μ - c`, `true_near` (Q3b) bounds it for a true attitude by the
error bounds, and `rotation_near` (Q3c) bounds the angle between two attitudes near the line of
`e`. -/

namespace Demos.Attitude

open Demos.Slew.Spec Demos.Slew.Arc Demos.Slew.Normalize Demos.Slew.Rotation Demos.Slew.Safety
open Demos.Slew.Premise Vec Real

/-- `e` is a unit quaternion that maximizes `qᵀ K q` on the unit sphere. -/
def IsMax (K : Sym4) (e : Quat) : Prop :=
  Quat.norm2 e = 1 ∧ ∀ q, Quat.norm2 q = 1 → K.form q ≤ K.form e

/-- The map `F` lies within `ε` of `G`: the images of every unit vector lie within angle `ε`. -/
def Within (F G : Vec → Vec) (ε : ℝ) : Prop := ∀ v, dot v v = 1 → vangle (F v) (G v) ≤ ε

/-! ### Quaternions as vectors of `ℝ⁴` -/

theorem quat_eq_zero {q : Quat} (h : Quat.norm2 q = 0) : q = ⟨0, 0, 0, 0⟩ := by
  simp only [Quat.norm2] at h
  ext
  · nlinarith [mul_self_nonneg q.w, mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
  · nlinarith [mul_self_nonneg q.w, mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
  · nlinarith [mul_self_nonneg q.w, mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]
  · nlinarith [mul_self_nonneg q.w, mul_self_nonneg q.x, mul_self_nonneg q.y, mul_self_nonneg q.z]

/-- The form vanishes at a quaternion of length zero. -/
theorem form_of_norm2_zero (K : Sym4) {q : Quat} (h : Quat.norm2 q = 0) : K.form q = 0 := by
  rw [quat_eq_zero h]; simp only [Sym4.form, qdot, Sym4.apply]; ring

theorem form_eq_unit (K : Sym4) {q : Quat} (hq : 0 < Quat.norm2 q) :
    K.form q = Quat.norm2 q * K.form (Quat.unit q) := by
  conv_lhs => rw [← quat_unit_smul q hq]
  rw [Sym4.form_qsmul, Real.sq_sqrt hq.le]

theorem qdot_unit (c : Quat) {q : Quat} (hq : 0 < Quat.norm2 q) :
    qdot (Quat.unit q) c = qdot q c / √(Quat.norm2 q) := by
  have : √(Quat.norm2 q) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  simp only [qdot, Quat.unit, Quat.smul]; field_simp

theorem unit_unit {q : Quat} (hq : 0 < Quat.norm2 q) : Quat.unit (Quat.unit q) = Quat.unit q :=
  unit_of_norm2_one (norm2_unit q hq)

/-! ### The maximizer -/

/-- **A maximizer exists**, by the compactness of the unit sphere of `ℝ⁴`. -/
theorem exists_isMax (K : Sym4) : ∃ e, IsMax K e := by
  let toQ : EuclideanSpace ℝ (Fin 4) → Quat := fun v => ⟨v 0, v 1, v 2, v 3⟩
  have hc : Continuous fun v : EuclideanSpace ℝ (Fin 4) => K.form (toQ v) := by
    have h0 := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
    have h1 := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 1
    have h2 := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 2
    have h3 := PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3
    simp only [Sym4.form, qdot, Sym4.apply, toQ]
    fun_prop
  have hn : ∀ v : EuclideanSpace ℝ (Fin 4), Quat.norm2 (toQ v) = ‖v‖ ^ 2 := by
    intro v
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    simp only [Quat.norm2, toQ]; ring
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 4)) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hc.continuousOn
  refine ⟨toQ v, ?_, fun q hq => ?_⟩
  · rw [hn, mem_sphere_zero_iff_norm.mp hv]; norm_num
  · let u : EuclideanSpace ℝ (Fin 4) := !₂[q.w, q.x, q.y, q.z]
    have hu : toQ u = q := by ext <;> simp [toQ, u]
    have hus : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
      rw [mem_sphere_zero_iff_norm]
      have h := hn u
      rw [hu, hq] at h
      exact (pow_left_inj₀ (norm_nonneg u) zero_le_one two_ne_zero).mp (by rw [one_pow]; exact h.symm)
    have := isMaxOn_iff.mp hmax u hus
    simpa only [hu] using this

theorem IsMax.form_le {K : Sym4} {e : Quat} (he : IsMax K e) (q : Quat) :
    K.form q ≤ K.form e * Quat.norm2 q := by
  rcases (norm2_nonneg q).lt_or_eq with hq | hq
  · rw [form_eq_unit K hq]
    have := he.2 _ (norm2_unit q hq)
    nlinarith
  · rw [form_of_norm2_zero K hq.symm, ← hq]; simp

/-- **A maximizer is an eigenvector** for the largest value `λ1 = eᵀ K e` of the form. -/
theorem IsMax.apply_eq {K : Sym4} {e : Quat} (he : IsMax K e) :
    K.apply e = Quat.smul (K.form e) e := by
  set v := qsub (K.apply e) (Quat.smul (K.form e) e) with hv
  have hKe : K.apply e = qadd v (Quat.smul (K.form e) e) := by
    ext <;> simp only [hv, qadd, qsub, Quat.smul] <;> ring
  have hve : qdot v e = 0 := by
    have e1 : qdot v e = K.form e - K.form e * Quat.norm2 e := by
      simp only [hv, Sym4.form, qdot, qsub, Quat.smul, Quat.norm2, Sym4.apply]; ring
    rw [e1, he.1]; ring
  have key : ∀ t : ℝ,
      2 * t * Quat.norm2 v + t ^ 2 * (K.form v - K.form e * Quat.norm2 v) ≤ 0 := by
    intro t
    have h := he.form_le (qadd e (Quat.smul t v))
    have e1 : K.form (qadd e (Quat.smul t v)) =
        K.form e + 2 * t * qdot v (K.apply e) + t ^ 2 * K.form v := by
      simp only [Sym4.form, qdot, Sym4.apply, qadd, Quat.smul]; ring
    have e2 : Quat.norm2 (qadd e (Quat.smul t v)) =
        Quat.norm2 e + 2 * t * qdot v e + t ^ 2 * Quat.norm2 v := by
      simp only [Quat.norm2, qdot, qadd, Quat.smul]; ring
    have e3 : qdot v (K.apply e) = Quat.norm2 v := by
      rw [hKe]
      have h1 : qdot v (qadd v (Quat.smul (K.form e) e)) =
          Quat.norm2 v + K.form e * qdot v e := by
        simp only [qdot, qadd, Quat.smul, Quat.norm2]; ring
      rw [h1, hve, mul_zero, add_zero]
    rw [e1, e2, e3, he.1, hve] at h
    nlinarith
  have hN0 : 0 ≤ Quat.norm2 v := norm2_nonneg v
  have hN : Quat.norm2 v = 0 := by
    generalize hNdef : Quat.norm2 v = N at key hN0
    generalize hCdef : K.form v - K.form e * N = C at key
    have hd : 0 < |C| + 1 := by positivity
    have h := key (N / (|C| + 1))
    have e1 : 2 * (N / (|C| + 1)) * N + (N / (|C| + 1)) ^ 2 * C =
        N ^ 2 * (2 * (|C| + 1) + C) / (|C| + 1) ^ 2 := by
      field_simp
    rw [e1, div_le_iff₀ (by positivity), zero_mul] at h
    have hC : 0 < 2 * (|C| + 1) + C := by linarith [neg_abs_le C, abs_nonneg C]
    have h3 : N ^ 2 ≤ 0 := by nlinarith
    exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h3 (sq_nonneg N))
  rw [hKe, quat_eq_zero hN]
  ext <;> simp only [qadd, Quat.smul] <;> ring

/-- The form at a vector perpendicular to `e` is at most `c` times its squared length, under the
cut, and below it for a nonzero vector. -/
theorem cut_le {K : Sym4} {e : Quat} {c : ℝ}
    (hcut : ∀ q, Quat.norm2 q = 1 → qdot q e = 0 → K.form q < c) {w : Quat} (hw : qdot w e = 0) :
    K.form w ≤ c * Quat.norm2 w := by
  rcases (norm2_nonneg w).lt_or_eq with hN | hN
  · rw [form_eq_unit K hN]
    have h := hcut _ (norm2_unit w hN) (by rw [qdot_unit e hN, hw, zero_div])
    nlinarith
  · rw [form_of_norm2_zero K hN.symm, ← hN]; simp

theorem cut_lt {K : Sym4} {e : Quat} {c : ℝ}
    (hcut : ∀ q, Quat.norm2 q = 1 → qdot q e = 0 → K.form q < c) {w : Quat} (hw : qdot w e = 0)
    (hN : 0 < Quat.norm2 w) : K.form w < c * Quat.norm2 w := by
  rw [form_eq_unit K hN]
  have h := hcut _ (norm2_unit w hN) (by rw [qdot_unit e hN, hw, zero_div])
  nlinarith

/-- **Q2, the inertia cut.**  If `K - c I` has a vector with a positive form and a hyperplane on
which its form is negative, as `onePos_of_pivots` gives, then for every maximizer `e`,
`c < λ1 = eᵀ K e` and every unit `q ⊥ e` has `qᵀ K q < c`. -/
theorem inertia_cut {K : Sym4} {c : ℝ} (h : (K.shift c).OnePos) {e : Quat} (he : IsMax K e) :
    c < K.form e ∧ ∀ q, Quat.norm2 q = 1 → qdot q e = 0 → K.form q < c := by
  obtain ⟨⟨u, hu⟩, d, hd⟩ := h
  have hlam : c < K.form e := by
    rw [Sym4.form_shift] at hu
    have h1 := he.form_le u
    have hN := norm2_nonneg u
    by_contra hle
    have hle := not_lt.mp hle
    nlinarith
  refine ⟨hlam, fun q hq hqe => ?_⟩
  by_contra hge
  have hge := not_lt.mp hge
  set A := K.shift c
  have hAe : A.apply e = Quat.smul (K.form e - c) e := by
    rw [Sym4.apply_shift, he.apply_eq]
    ext <;> simp only [qsub, Quat.smul] <;> ring
  have hAeq : qdot e (A.apply q) = 0 := by
    rw [Sym4.qdot_apply, hAe]
    have : qdot (Quat.smul (K.form e - c) e) q = (K.form e - c) * qdot q e := by
      simp only [qdot, Quat.smul]; ring
    rw [this, hqe, mul_zero]
  set α := qdot d q
  set β := -qdot d e
  set v := qadd (Quat.smul α e) (Quat.smul β q)
  have hdv : qdot d v = 0 := by simp only [v, α, β, qdot, qadd, Quat.smul]; ring
  have hform : A.form v = α ^ 2 * A.form e + β ^ 2 * A.form q := by
    have e1 : A.form v = α ^ 2 * A.form e + 2 * α * β * qdot e (A.apply q) + β ^ 2 * A.form q := by
      simp only [Sym4.form, v, qdot, Sym4.apply, qadd, Quat.smul]; ring
    rw [e1, hAeq]; ring
  have hAe_pos : 0 < A.form e := by rw [Sym4.form_shift, he.1]; linarith
  have hAq : 0 ≤ A.form q := by rw [Sym4.form_shift, hq]; linarith
  have hnv : Quat.norm2 v = α ^ 2 + β ^ 2 := by
    have e1 : Quat.norm2 v = α ^ 2 * Quat.norm2 e + 2 * α * β * qdot q e + β ^ 2 * Quat.norm2 q := by
      simp only [v, Quat.norm2, qdot, qadd, Quat.smul]; ring
    rw [e1, he.1, hq, hqe]; ring
  by_cases hab : 0 < α ^ 2 + β ^ 2
  · have h1 := hd v hdv (by rw [hnv]; exact hab)
    have h2 : 0 ≤ A.form v := by
      rw [hform]; have := sq_nonneg α; have := sq_nonneg β; positivity
    linarith
  · have hβ : β = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    have hde : qdot d e = 0 := by simp only [β] at hβ; linarith
    have := hd e hde (by rw [he.1]; norm_num)
    linarith

/-- **The maximizer is unique up to sign** under the inertia certificate. -/
theorem isMax_unique {K : Sym4} {c : ℝ} (h : (K.shift c).OnePos) {e e' : Quat} (he : IsMax K e)
    (he' : IsMax K e') : e' = e ∨ e' = qneg e := by
  obtain ⟨hlam, hcut⟩ := inertia_cut h he
  have heq : K.form e' = K.form e := le_antisymm (he.2 _ he'.1) (he'.2 _ he.1)
  set a := qdot e' e
  set w := qsub e' (Quat.smul a e)
  have hwe : qdot w e = 0 := by
    have e1 : qdot w e = qdot e' e - a * Quat.norm2 e := by
      simp only [w, qdot, qsub, Quat.smul, Quat.norm2]; ring
    rw [e1, he.1]; ring
  have he'w : e' = qadd w (Quat.smul a e) := by
    ext <;> simp only [w, qadd, qsub, Quat.smul] <;> ring
  have hform : K.form e' = K.form w + a ^ 2 * K.form e := by
    have e1 : K.form (qadd w (Quat.smul a e)) =
        K.form w + 2 * a * qdot w (K.apply e) + a ^ 2 * K.form e := by
      simp only [Sym4.form, qdot, Sym4.apply, qadd, Quat.smul]; ring
    have e2 : qdot w (K.apply e) = K.form e * qdot w e := by
      rw [he.apply_eq]; simp only [qdot, Quat.smul]; ring
    rw [he'w, e1, e2, hwe]; ring
  have hnw : Quat.norm2 w = 1 - a ^ 2 := by
    have e1 : Quat.norm2 (qadd w (Quat.smul a e)) =
        Quat.norm2 w + 2 * a * qdot w e + a ^ 2 * Quat.norm2 e := by
      simp only [Quat.norm2, qdot, qadd, Quat.smul]; ring
    have := he'.1
    rw [he'w, e1, hwe, he.1] at this
    linarith
  by_cases hw : 0 < Quat.norm2 w
  · have h1 := cut_lt hcut hwe hw
    rw [hnw] at h1 hw
    nlinarith
  · have hw0 : Quat.norm2 w = 0 := le_antisymm (not_lt.mp hw) (norm2_nonneg w)
    have ha : (a - 1) * (a + 1) = 0 := by linarith
    rw [he'w, quat_eq_zero hw0]
    rcases mul_eq_zero.mp ha with h1 | h1
    · left
      have : a = 1 := by linarith
      rw [this]; ext <;> simp only [qadd, Quat.smul] <;> ring
    · right
      have : a = -1 := by linarith
      rw [this]; ext <;> simp only [qadd, Quat.smul, qneg] <;> ring

/-! ### The angle bounds -/

/-- The Davis–Kahan bound for any quaternion `p` and any `μ > c`, in squared form. -/
theorem davis_kahan_sq {K : Sym4} {e : Quat} {c μ : ℝ} (he : IsMax K e)
    (hcut : ∀ q, Quat.norm2 q = 1 → qdot q e = 0 → K.form q < c) (hμ : c < μ) (p : Quat) :
    (μ - c) ^ 2 * (Quat.norm2 p - qdot p e ^ 2) ≤
      Quat.norm2 (qsub (K.apply p) (Quat.smul μ p)) := by
  set a := qdot p e
  set w := qsub p (Quat.smul a e)
  have hwe : qdot w e = 0 := by
    have e1 : qdot w e = qdot p e - a * Quat.norm2 e := by
      simp only [w, qdot, qsub, Quat.smul, Quat.norm2]; ring
    rw [e1, he.1]; ring
  have hnw : Quat.norm2 w = Quat.norm2 p - a ^ 2 := by
    have e1 : Quat.norm2 w = Quat.norm2 p - 2 * a * qdot p e + a ^ 2 * Quat.norm2 e := by
      simp only [w, Quat.norm2, qdot, qsub, Quat.smul]; ring
    rw [e1, he.1]; ring
  set Dw := qsub (K.apply w) (Quat.smul μ w)
  have hDp : qsub (K.apply p) (Quat.smul μ p) = qadd Dw (Quat.smul (a * (K.form e - μ)) e) := by
    have hKp : K.apply p = qadd (K.apply w) (Quat.smul a (K.apply e)) := by
      ext <;> simp only [Sym4.apply, w, qsub, qadd, Quat.smul] <;> ring
    rw [hKp, he.apply_eq]
    ext <;> simp only [Dw, w, qsub, qadd, Quat.smul] <;> ring
  have hDwe : qdot Dw e = 0 := by
    have e1 : qdot Dw e = qdot w (K.apply e) - μ * qdot w e := by
      simp only [Dw, qdot, qsub, Quat.smul, Sym4.apply]; ring
    rw [e1, he.apply_eq]
    simp only [qdot, Quat.smul] at hwe ⊢
    linear_combination (K.form e - μ) * hwe
  have hDp2 : Quat.norm2 Dw ≤ Quat.norm2 (qsub (K.apply p) (Quat.smul μ p)) := by
    rw [hDp]
    have e1 : Quat.norm2 (qadd Dw (Quat.smul (a * (K.form e - μ)) e)) =
        Quat.norm2 Dw + 2 * (a * (K.form e - μ)) * qdot Dw e +
          (a * (K.form e - μ)) ^ 2 * Quat.norm2 e := by
      simp only [Quat.norm2, qdot, qadd, Quat.smul]; ring
    rw [e1, hDwe, he.1]
    nlinarith [sq_nonneg (a * (K.form e - μ))]
  set N := Quat.norm2 w
  have hN0 : 0 ≤ N := norm2_nonneg w
  have hcs := qdot_sq_le w Dw
  have hqd : qdot w Dw = K.form w - μ * N := by
    simp only [Dw, Sym4.form, N, qdot, qsub, Quat.smul, Quat.norm2]; ring
  have h1 : (μ - c) * N ≤ -qdot w Dw := by rw [hqd]; linarith [cut_le hcut hwe]
  have h0 : 0 ≤ (μ - c) * N := mul_nonneg (by linarith) hN0
  have h2 : ((μ - c) * N) ^ 2 ≤ N * Quat.norm2 Dw := by
    calc ((μ - c) * N) ^ 2 ≤ qdot w Dw ^ 2 := by nlinarith
      _ ≤ N * Quat.norm2 Dw := hcs
  have h3 : (μ - c) ^ 2 * N ≤ Quat.norm2 Dw := by
    rcases hN0.lt_or_eq with hN | hN
    · have h4 : N * ((μ - c) ^ 2 * N) ≤ N * Quat.norm2 Dw := by nlinarith
      exact le_of_mul_le_mul_left h4 hN
    · rw [← hN, mul_zero]; exact norm2_nonneg _
  rw [← hnw]
  linarith

/-- **Q3, the Davis–Kahan bound for one vector.**  Under the cut of Q2, the component of a unit
`v` perpendicular to `e` has length at most `|K v - μ v| / (μ - c)` for every `μ > c`. -/
theorem davis_kahan {K : Sym4} {e : Quat} {c μ : ℝ} (he : IsMax K e)
    (hcut : ∀ q, Quat.norm2 q = 1 → qdot q e = 0 → K.form q < c) (hμ : c < μ) {v : Quat}
    (hv : Quat.norm2 v = 1) :
    √(1 - qdot v e ^ 2) ≤ qnorm (qsub (K.apply v) (Quat.smul μ v)) / (μ - c) := by
  have h := davis_kahan_sq he hcut hμ v
  rw [hv] at h
  have hμc : 0 < μ - c := by linarith
  rw [le_div_iff₀ hμc, qnorm]
  calc √(1 - qdot v e ^ 2) * (μ - c) = √((μ - c) ^ 2 * (1 - qdot v e ^ 2)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hμc.le, mul_comm]
    _ ≤ _ := Real.sqrt_le_sqrt h

/-- The Davis–Kahan bound for a nonzero `p` normalized: when `|K p - μ p|² ≤ ρ² |p|²` and
`μ > c`, the squared sine of the angle between `p̄` and the line of `e` is at most
`(ρ / (μ - c))²`. -/
theorem sin_sq_le_of_resid {K : Sym4} {e : Quat} {c μ ρ : ℝ} (he : IsMax K e)
    (hcut : ∀ q, Quat.norm2 q = 1 → qdot q e = 0 → K.form q < c) (hμ : c < μ) {p : Quat}
    (hp : 0 < Quat.norm2 p)
    (hρ : Quat.norm2 (qsub (K.apply p) (Quat.smul μ p)) ≤ ρ ^ 2 * Quat.norm2 p) :
    1 - qdot (Quat.unit p) e ^ 2 ≤ (ρ / (μ - c)) ^ 2 := by
  have h := davis_kahan_sq he hcut hμ p
  have hμc : 0 < μ - c := by linarith
  rw [qdot_unit e hp, div_pow, Real.sq_sqrt hp.le, div_pow]
  rw [show 1 - qdot p e ^ 2 / Quat.norm2 p = (Quat.norm2 p - qdot p e ^ 2) / Quat.norm2 p by
    field_simp]
  rw [div_le_div_iff₀ hp (by positivity)]
  nlinarith

/-- **Q3b.**  For observations with nonzero vectors, weights at least zero, and error bounds in
`[0, π/2]`, under the cut of Q2 for `c < μ_t`, every nonzero `q` whose attitude meets the error
bounds has `1 - (q̄ · e)² ≤ (ρ_t / (μ_t - c))²` for `q̄ = q / |q|`, where `ρ_t = Σ a_i sin ε_i` and
`μ_t = Σ a_i cos ε_i`: the line of `q̄` lies within the angle `arcsin (ρ_t / (μ_t - c))` of the
line of `e`. -/
theorem true_near {o : ℕ → Obs} {n : ℕ} (hb : ∀ i < n, 0 < norm (o i).b)
    (hr : ∀ i < n, 0 < norm (o i).r) (ha : ∀ i < n, 0 ≤ (o i).a) (hε0 : ∀ i < n, 0 ≤ (o i).ε)
    (hε : ∀ i < n, (o i).ε ≤ π / 2) {e : Quat} {c : ℝ} (he : IsMax (davK o n) e)
    (hcut : ∀ q, Quat.norm2 q = 1 → qdot q e = 0 → (davK o n).form q < c)
    (hμ : c < ∑ i ∈ Finset.range n, (o i).a * cos (o i).ε) {q : Quat} (hq : 0 < Quat.norm2 q)
    (h : ∀ i < n, vangle (attitude q (unit (o i).b)) (unit (o i).r) ≤ (o i).ε) :
    1 - qdot (Quat.unit q) e ^ 2 ≤
      ((∑ i ∈ Finset.range n, (o i).a * sin (o i).ε) /
        (∑ i ∈ Finset.range n, (o i).a * cos (o i).ε - c)) ^ 2 := by
  set K := davK o n
  set Q := Quat.unit q
  have hQ : Quat.norm2 Q = 1 := norm2_unit q hq
  have hQatt : ∀ v, attitude Q v = attitude q v := by
    intro v; simp only [attitude, Q, unit_unit hq]
  have h' : ∀ i < n, vangle (attitude Q (unit (o i).b)) (unit (o i).r) ≤ (o i).ε := by
    intro i hi; rw [hQatt]; exact h i hi
  have hform := true_form hb hr ha (fun i hi => by linarith [hε i hi, pi_pos]) hQ h'
  have hres := true_resid hb hr ha hε0 hε hQ h'
  set ρt := ∑ i ∈ Finset.range n, (o i).a * sin (o i).ε
  set μt := ∑ i ∈ Finset.range n, (o i).a * cos (o i).ε
  have hρ0 : 0 ≤ ρt := le_trans (qnorm_nonneg _) hres
  have hd := davis_kahan_sq he hcut (lt_of_lt_of_le hμ hform) Q
  rw [hQ] at hd
  have hR : Quat.norm2 (qsub (K.apply Q) (Quat.smul (K.form Q) Q)) ≤ ρt ^ 2 := by
    have h2 := mul_self_le_mul_self (qnorm_nonneg _) hres
    rw [qnorm_sq] at h2
    simpa [Sym4.resid, sq] using h2
  have hμ1 : 0 < μt - c := by linarith
  have hμ2 : μt - c ≤ K.form Q - c := by linarith
  rw [div_pow, le_div_iff₀ (by positivity)]
  have hs : 0 ≤ 1 - qdot Q e ^ 2 := by
    have := qdot_sq_le Q e; rw [hQ, he.1] at this; linarith
  calc (1 - qdot Q e ^ 2) * (μt - c) ^ 2 ≤ (1 - qdot Q e ^ 2) * (K.form Q - c) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ1.le hμ2 2) hs
    _ ≤ ρt ^ 2 := by nlinarith

/-- `|p · q| ≥ |p · e| |q · e| - √(1 - (p · e)²) √(1 - (q · e)²)` for unit `p`, `q`, `e`. -/
theorem abs_qdot_ge {p q e : Quat} (hp : Quat.norm2 p = 1) (hq : Quat.norm2 q = 1)
    (he : Quat.norm2 e = 1) :
    |qdot p e| * |qdot q e| - √(1 - qdot p e ^ 2) * √(1 - qdot q e ^ 2) ≤ |qdot p q| := by
  set a := qdot p e
  set b := qdot q e
  set P := qsub p (Quat.smul a e)
  set Q := qsub q (Quat.smul b e)
  have hPQ : qdot P Q = qdot p q - a * b := by
    have e1 : qdot P Q = qdot p q - b * qdot p e - a * qdot e q + a * b * Quat.norm2 e := by
      simp only [P, Q, qdot, qsub, Quat.smul, Quat.norm2]; ring
    rw [e1, he, qdot_comm e q]; ring
  have hP : Quat.norm2 P = 1 - a ^ 2 := by
    have e1 : Quat.norm2 P = Quat.norm2 p - 2 * a * qdot p e + a ^ 2 * Quat.norm2 e := by
      simp only [P, Quat.norm2, qdot, qsub, Quat.smul]; ring
    rw [e1, hp, he]; ring
  have hQ : Quat.norm2 Q = 1 - b ^ 2 := by
    have e1 : Quat.norm2 Q = Quat.norm2 q - 2 * b * qdot q e + b ^ 2 * Quat.norm2 e := by
      simp only [Q, Quat.norm2, qdot, qsub, Quat.smul]; ring
    rw [e1, hq, he]; ring
  have hcs := qdot_sq_le P Q
  rw [hPQ, hP, hQ] at hcs
  have ha1 : 0 ≤ 1 - a ^ 2 := by rw [← hP]; exact norm2_nonneg _
  have hb1 : 0 ≤ 1 - b ^ 2 := by rw [← hQ]; exact norm2_nonneg _
  have hdiff : |qdot p q - a * b| ≤ √(1 - a ^ 2) * √(1 - b ^ 2) := by
    rw [← Real.sqrt_mul ha1, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hcs
  have hab : |a| * |b| = |a * b| := (abs_mul a b).symm
  rw [hab]
  have := abs_sub_abs_le_abs_sub (a * b) (qdot p q)
  rw [abs_sub_comm] at this
  linarith

/-- `cos ε ≤ |x|` for `|x| ≤ 1` and `ε` in `[0, π/2]` gives `√(1 - x²) ≤ sin ε`. -/
theorem sqrt_one_sub_le_sin {x ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ π / 2) (h : cos ε ≤ |x|) :
    √(1 - x ^ 2) ≤ sin ε := by
  have hs0 : 0 ≤ sin ε := sin_nonneg_of_nonneg_of_le_pi hε0 (by linarith [pi_pos])
  have hc0 : 0 ≤ cos ε := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hε1⟩
  rw [← Real.sqrt_sq hs0]
  apply Real.sqrt_le_sqrt
  have h1 : cos ε ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ hc0 h 2
  have := sin_sq_add_cos_sq ε
  linarith

/-- The action of unit `p` and of unit `q` on a vector have the inner product of `v` with the
action of `q* p` on it. -/
theorem dot_act_act {p q : Quat} (hq : Quat.norm2 q = 1) (v : Vec) :
    dot (act p v) (act q v) = dot v (act (qmul (conj q) p) v) := by
  have hc : Quat.norm2 (conj q) = 1 := by rw [norm2_conj, hq]
  rw [← dot_act_one hc, ← act_qmul, ← act_qmul, conj_qmul_self q hq, dot_comm]
  congr 1
  ext <;> simp only [act, vpart, qmul, conj, one, Demos.Slew.Rotation.pure] <;> ring

/-- **Q3c.**  Unit quaternions `p` and `q` whose lines lie within the angles `α` and `β` of the
line of a unit `e`, `|p · e| ≥ cos α` and `|q · e| ≥ cos β` with `α`, `β` in `[0, π/2]`, have
attitudes within `2 (α + β)` of each other. -/
theorem rotation_near {p q e : Quat} (hp : Quat.norm2 p = 1) (hq : Quat.norm2 q = 1)
    (he : Quat.norm2 e = 1) {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ π / 2) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ π / 2) (hpa : cos α ≤ |qdot p e|) (hqb : cos β ≤ |qdot q e|) :
    Within (act p) (act q) (2 * (α + β)) := by
  intro v hv
  by_cases hs : π / 2 ≤ α + β
  · have := InnerProductGeometry.angle_le_pi (toE (act p v)) (toE (act q v))
    rw [← vangle] at this
    linarith
  replace hs := not_le.mp hs
  -- the inner product of the two quaternions
  have hca : 0 ≤ cos α := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hα1⟩
  have hcb : 0 ≤ cos β := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hβ1⟩
  have hsa := sqrt_one_sub_le_sin hα0 hα1 hpa
  have hsb := sqrt_one_sub_le_sin hβ0 hβ1 hqb
  have hpq := abs_qdot_ge hp hq he
  have hcos : cos (α + β) ≤ |qdot p q| := by
    rw [cos_add]
    have h1 : cos α * cos β ≤ |qdot p e| * |qdot q e| := mul_le_mul hpa hqb hcb (abs_nonneg _)
    have h2 : √(1 - qdot p e ^ 2) * √(1 - qdot q e ^ 2) ≤ sin α * sin β :=
      mul_le_mul hsa hsb (Real.sqrt_nonneg _)
        (sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith [pi_pos]))
    linarith
  have hc0 : 0 ≤ cos (α + β) := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hs.le⟩
  -- the angle of the relative rotation
  set Q := qmul (conj q) p
  have hQ : Quat.norm2 Q = 1 := by
    rw [norm2_qmul, norm2_conj, hq, hp]; ring
  have hQw : Q.w = qdot p q := by simp only [Q, qmul, conj, qdot]; ring
  have hge := dot_act_self_ge Q v
  rw [hQ, hQw, hv] at hge
  have hp1 : dot (act p v) (act p v) = 1 := by rw [dot_act, hp, hv]; ring
  have hq1 : dot (act q v) (act q v) = 1 := by rw [dot_act, hq, hv]; ring
  apply vangle_le hp1 hq1 (by linarith) (by linarith)
  rw [dot_act_act hq, cos_two_mul]
  have h3 : cos (α + β) ^ 2 ≤ qdot p q ^ 2 := by
    rw [← sq_abs (qdot p q)]; exact pow_le_pow_left₀ hc0 hcos 2
  nlinarith

/-- Q3c with the sines of the angles: nonzero `p` and `q` whose normalizations satisfy
`1 - (p̄ · e)² ≤ s²` and `1 - (q̄ · e)² ≤ t²` for `s`, `t` in `[0, 1]` have attitudes within
`2 (arcsin s + arcsin t)` of each other. -/
theorem within_of_sin {p q e : Quat} (hp : 0 < Quat.norm2 p) (hq : 0 < Quat.norm2 q)
    (he : Quat.norm2 e = 1) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hps : 1 - qdot (Quat.unit p) e ^ 2 ≤ s ^ 2) (hqt : 1 - qdot (Quat.unit q) e ^ 2 ≤ t ^ 2) :
    Within (attitude p) (attitude q) (2 * (arcsin s + arcsin t)) := by
  have hcos : ∀ {x u : ℝ}, 0 ≤ u → u ≤ 1 → 1 - x ^ 2 ≤ u ^ 2 → cos (arcsin u) ≤ |x| := by
    intro x u hu0 hu1 h
    rw [cos_arcsin, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  intro v hv
  rw [attitude_eq hp, attitude_eq hq]
  exact rotation_near (norm2_unit p hp) (norm2_unit q hq) he (arcsin_nonneg.mpr hs0)
    (arcsin_le_pi_div_two s) (arcsin_nonneg.mpr ht0) (arcsin_le_pi_div_two t)
    (hcos hs0 hs1 hps) (hcos ht0 ht1 hqt) v hv

end Demos.Attitude
