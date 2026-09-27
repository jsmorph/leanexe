import Project.SpectralKL.CertificateBounds

namespace Project.SpectralKL.MatrixIteration
open Matrix Finset
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def normSq (v : n → ℝ) : ℝ := v ⬝ᵥ v
def frobSq (A : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, (A i j)^2

theorem normSq_nonneg (v : n → ℝ) : 0 ≤ normSq v := Residual.self_nonneg v

theorem normSq_smul (c : ℝ) (v : n → ℝ) :
    normSq (c • v) = c^2 * normSq v := by
  simp [normSq, smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two, mul_assoc]

theorem mulVec_bound (A : Matrix n n ℝ) (v : n → ℝ) :
    normSq (A *ᵥ v) ≤ frobSq A * normSq v := by
  simp only [normSq, dotProduct, mulVec, ← pow_two]
  calc
    ∑ i, (∑ j, A i j * v j)^2 ≤ ∑ i, (∑ j, (A i j)^2)*(∑ j, (v j)^2) := by
      apply sum_le_sum
      intro i _
      exact sum_mul_sq_le_sq_mul_sq univ (fun j => A i j) v
    _ = frobSq A * ∑ j, (v j)^2 := by rw [frobSq, sum_mul]

theorem mixed_frob (A B : Matrix n n ℝ) (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) :
    frobSq (r • A + (1-r) • B) ≤ frobSq A + frobSq B := by
  simp only [frobSq, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  have h := Certificate.convex_square (B i j) (A i j) r hr
  simpa only [add_comm] using h

/-- Richardson iteration, evaluated at a fixed integration parameter.
The executable polynomial version computes all parameters simultaneously. -/
noncomputable def iterate (S : Matrix n n ℝ) (eta : ℝ) (d : n → ℝ) : Nat → n → ℝ
  | 0 => 0
  | k+1 => (1/eta) • (d-S *ᵥ iterate S eta d k)

noncomputable def residual (S : Matrix n n ℝ) (eta : ℝ) (d : n → ℝ) (k : Nat) : n → ℝ :=
  d-(S+eta • 1) *ᵥ iterate S eta d k

theorem residual_zero (S : Matrix n n ℝ) (eta : ℝ) (d : n → ℝ) :
    residual S eta d 0 = d := by simp [residual, iterate]

theorem residual_succ (S : Matrix n n ℝ) (eta : ℝ) (he : eta ≠ 0)
    (d : n → ℝ) (k : Nat) :
    residual S eta d (k+1) = (-1/eta) • (S *ᵥ residual S eta d k) := by
  simp only [residual, iterate, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_add,
    smul_sub, smul_add, smul_smul]
  have hcancel : (1/eta) * eta = 1 := by field_simp
  have hcancel' : (-1/eta)*eta = -1 := by field_simp
  simp only [hcancel, hcancel', one_smul]
  module

theorem residual_bound_with (A B : Matrix n n ℝ) (eta : ℝ) (he : 0 < eta)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hAB : frobSq A + frobSq B ≤ rho*eta^2)
    (d : n → ℝ) (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) (k : Nat) :
    normSq (residual (r • A+(1-r) • B) eta d k) ≤ rho^k * normSq d := by
  let S := r • A+(1-r) • B
  have hS : frobSq S ≤ rho*eta^2 := (mixed_frob A B r hr).trans hAB
  have hstep (v : n → ℝ) : normSq ((-1/eta) • (S *ᵥ v)) ≤ rho*normSq v := by
    rw [normSq_smul]
    have h := mulVec_bound S v
    have hi := mul_le_mul_of_nonneg_right hS (normSq_nonneg v)
    have hdiv : (-1/eta)^2 = 1/eta^2 := by field_simp
    rw [hdiv, one_div, ← div_eq_inv_mul]
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    nlinarith
  induction k with
  | zero => simp [residual_zero]
  | succ k ih =>
    rw [residual_succ _ _ he.ne']
    have hs := hstep (residual S eta d k)
    have hm := mul_le_mul_of_nonneg_left ih hrho
    rw [pow_succ]
    dsimp [S] at hs
    nlinarith

#print axioms residual_bound_with
end Project.SpectralKL.MatrixIteration
