import Project.SpectralKL.MatrixAdaptive

namespace Project.SpectralKL.MatrixDamped
open Matrix Finset MatrixIteration
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem normSq_add_le (v w : n → ℝ) :
    normSq (v+w) ≤ 2*normSq v+2*normSq w := by
  simp only [normSq,dotProduct,Pi.add_apply,Finset.mul_sum,← Finset.sum_add_distrib]
  apply sum_le_sum
  intro i _
  nlinarith [sq_nonneg (v i-w i)]

theorem normSq_sub_smul (v w : n → ℝ) (a : ℝ) :
    normSq (v-a • w) = normSq v-2*a*(v ⬝ᵥ w)+a^2*normSq w := by
  simp only [normSq,sub_dotProduct,dotProduct_sub,smul_dotProduct,dotProduct_smul,
    smul_eq_mul,dotProduct_comm w v]
  ring

/-- A stored polynomial implementation below realizes this damped Richardson recurrence. -/
noncomputable def iterate (H : Matrix n n ℝ) (a : ℝ) (d : n → ℝ) : Nat → n → ℝ
  | 0 => 0
  | k+1 => let x := iterate H a d k; x+a • (d-H *ᵥ x)

noncomputable def residual (H : Matrix n n ℝ) (a : ℝ) (d : n → ℝ) (k : Nat) : n → ℝ :=
  d-H *ᵥ iterate H a d k

theorem residual_succ (H : Matrix n n ℝ) (a : ℝ) (d : n → ℝ) (k : Nat) :
    residual H a d (k+1) = residual H a d k-a • (H *ᵥ residual H a d k) := by
  simp only [residual,iterate,Matrix.mulVec_add,Matrix.mulVec_smul]
  module

theorem step_bound (H : Matrix n n ℝ) (eta U : ℝ) (he : 0 < eta) (hU : 0 < U)
    (hc : Residual.Coercive H eta)
    (hn : ∀ v, normSq (H *ᵥ v) ≤ U*normSq v) (v : n → ℝ) :
    normSq (v-(eta/U) • (H *ᵥ v)) ≤ (1-eta^2/U)*normSq v := by
  rw [normSq_sub_smul]
  have ha : 0 ≤ eta/U := div_nonneg he.le hU.le
  have h1 := mul_le_mul_of_nonneg_left (hc v) (show 0 ≤ 2*(eta/U) by positivity)
  have h2 := mul_le_mul_of_nonneg_left (hn v) (sq_nonneg (eta/U))
  have hid : normSq v-2*(eta/U)*(eta*normSq v)+(eta/U)^2*(U*normSq v) =
      (1-eta^2/U)*normSq v := by field_simp; ring
  dsimp only [normSq] at *
  linarith

noncomputable def upperSq (p q : List (n → ℝ)) (eta : ℝ) : ℝ :=
  2*(eta^2+frobSq (Samples.moment p)+frobSq (Samples.moment q))

theorem upperSq_pos (p q : List (n → ℝ)) (eta : ℝ) (he : 0 < eta) :
    0 < upperSq p q eta := by
  have hp : 0 ≤ frobSq (Samples.moment p) := by unfold frobSq; positivity
  have hq : 0 ≤ frobSq (Samples.moment q) := by unfold frobSq; positivity
  unfold upperSq
  positivity

theorem system_bound (p q : List (n → ℝ)) (eta r : ℝ)
    (hr : r ∈ Set.Icc (0:ℝ) 1) (v : n → ℝ) :
    normSq (Samples.system p q eta r *ᵥ v) ≤ upperSq p q eta*normSq v := by
  let S := r • Samples.moment p+(1-r) • Samples.moment q
  have hS := (mulVec_bound S v).trans
    (mul_le_mul_of_nonneg_right (mixed_frob _ _ r hr) (normSq_nonneg v))
  have h := normSq_add_le (S *ᵥ v) (eta • v)
  rw [normSq_smul] at h
  simp only [Samples.system,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  simp only [S,Matrix.add_mulVec,Matrix.smul_mulVec] at h hS
  unfold upperSq
  nlinarith

theorem residual_bound (p q : List (n → ℝ)) (eta : ℝ) (he : 0 < eta)
    (d : n → ℝ) (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) (k : Nat) :
    normSq (residual (Samples.system p q eta r) (eta/upperSq p q eta) d k) ≤
      (1-eta^2/upperSq p q eta)^k * normSq d := by
  have hU := upperSq_pos p q eta he
  have hp : 0 ≤ frobSq (Samples.moment p) := by unfold frobSq; positivity
  have hq : 0 ≤ frobSq (Samples.moment q) := by unfold frobSq; positivity
  have hrho : 0 ≤ 1-eta^2/upperSq p q eta := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hU).mpr
    unfold upperSq
    nlinarith [sq_nonneg eta]
  induction k with
  | zero => simp [residual,iterate]
  | succ k ih =>
    rw [residual_succ]
    have hs := step_bound (Samples.system p q eta r) eta (upperSq p q eta) he hU
      (Samples.system_coercive p q eta r hr) (system_bound p q eta r hr)
      (residual (Samples.system p q eta r) (eta/upperSq p q eta) d k)
    exact hs.trans (by simpa [pow_succ,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left ih hrho)

#print axioms residual_bound
end Project.SpectralKL.MatrixDamped
