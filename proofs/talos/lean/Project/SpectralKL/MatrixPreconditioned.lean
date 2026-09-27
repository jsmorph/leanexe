import Project.SpectralKL.MatrixEnergyBound
import Project.SpectralKL.ExactInverse

namespace Project.SpectralKL.MatrixPreconditioned
open Matrix Finset MatrixIteration MatrixPolynomial MatrixEstimator Samples DensePolynomial
open scoped Matrix
variable {m : Nat}

theorem mixed_frob_max (A B : Matrix (Fin m) (Fin m) ℝ) (r : ℝ)
    (hr : r ∈ Set.Icc (0:ℝ) 1) :
    frobSq (r • A+(1-r) • B) ≤ max (frobSq A) (frobSq B) := by
  have hw : 0 ≤ 1-r := sub_nonneg.mpr hr.2
  have hc : frobSq (r • A+(1-r) • B) ≤ r*frobSq A+(1-r)*frobSq B := by
    simp only [frobSq,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    nlinarith [mul_nonneg (mul_nonneg hr.1 hw) (sq_nonneg (A i j-B i j))]
  calc
    _ ≤ r*frobSq A+(1-r)*frobSq B := hc
    _ ≤ r*max (frobSq A) (frobSq B)+(1-r)*max (frobSq A) (frobSq B) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hr.1)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hw)
    _ = _ := by ring

noncomputable def iterate (H M : Matrix (Fin m) (Fin m) ℝ) (d : Fin m → ℝ) : Nat → Fin m → ℝ
  | 0 => 0
  | k+1 => let x := iterate H M d k; x+M *ᵥ (d-H *ᵥ x)

theorem residual_succ (H M : Matrix (Fin m) (Fin m) ℝ) (d : Fin m → ℝ) (k : Nat) :
    d-H *ᵥ iterate H M d (k+1) = (1-H*M) *ᵥ (d-H *ᵥ iterate H M d k) := by
  simp only [iterate,Matrix.mulVec_add,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.mulVec_mulVec]
  module

theorem mixed_error (A B M : Matrix (Fin m) (Fin m) ℝ) (eta r : ℝ) :
    1-(r • A+(1-r) • B+eta • 1)*M =
      r • (1-(A+eta • 1)*M)+(1-r) • (1-(B+eta • 1)*M) := by
  simp only [Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,smul_sub,smul_add,smul_smul]
  module

theorem residual_bound (A B M : Matrix (Fin m) (Fin m) ℝ) (eta : ℝ)
    (d : Fin m → ℝ) (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) (k : Nat) :
    normSq (d-(r • A+(1-r) • B+eta • 1) *ᵥ
      iterate (r • A+(1-r) • B+eta • 1) M d k) ≤
      (max (frobSq (1-(A+eta • 1)*M)) (frobSq (1-(B+eta • 1)*M)))^k*normSq d := by
  let H := r • A+(1-r) • B+eta • 1
  let rho := max (frobSq (1-(A+eta • 1)*M)) (frobSq (1-(B+eta • 1)*M))
  have hrho : 0 ≤ rho := by dsimp [rho,frobSq]; positivity
  have hK : frobSq (1-H*M) ≤ rho := by
    dsimp only [H]
    rw [mixed_error]
    exact mixed_frob_max _ _ r hr
  change normSq (d-H *ᵥ iterate H M d k) ≤ rho^k*normSq d
  induction k with
  | zero => simp [iterate,Matrix.mulVec_zero]
  | succ k ih =>
    rw [residual_succ]
    calc
      _ ≤ frobSq (1-H*M)*normSq (d-H *ᵥ iterate H M d k) := mulVec_bound _ _
      _ ≤ rho*normSq (d-H *ᵥ iterate H M d k) := mul_le_mul_of_nonneg_right hK (normSq_nonneg _)
      _ ≤ rho*(rho^k*normSq d) := mul_le_mul_of_nonneg_left ih hrho
      _ = rho^(k+1)*normSq d := by ring

/-- Each residual and each iterate is stored, so the matrix products are computed once. -/
def solution (A B M : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (eta : ℚ) :
    Nat → Vector Poly m
  | 0 => store (fun _ => [])
  | k+1 =>
    let x := solution A B M d eta k
    let e := store (fun i => sub [d i]
      (add (sumTerms (fun j => mul (MatrixPolynomial.system A B i j) (view x j)))
        (scale eta (view x i))))
    store (fun i => add (view x i) (sumTerms (fun j => scale (M i j) (view e j))))

theorem solution_eval (A B M : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    (eta : ℚ) (k : Nat) (r : ℝ) :
    (fun i => eval (view (solution A B M d eta k) i) r) =
      iterate (r • realMatrix A+(1-r) • realMatrix B+(eta:ℝ) • 1)
        (realMatrix M) (realVec d) k := by
  induction k with
  | zero => ext i; simp [solution,iterate,eval]
  | succ k ih =>
    ext i
    simp only [solution,view_store,eval_add,eval_scale,eval_sub,eval_sumTerms,eval_mul,
      system_eval,iterate,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
      Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Matrix.mulVec,dotProduct]
    simp_rw [congrFun ih]
    simp [eval,realVec,realMatrix,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]

def contraction (A B M : Matrix (Fin m) (Fin m) ℚ) (eta : ℚ) : ℚ :=
  max (frobSqQ (1-(A+eta • 1)*M)) (frobSqQ (1-(B+eta • 1)*M))

theorem real_error (A M : Matrix (Fin m) (Fin m) ℚ) (eta : ℚ) :
    realMatrix (1-(A+eta • 1)*M) = 1-(realMatrix A+(eta:ℝ) • 1)*realMatrix M := by
  ext i j
  simp [realMatrix,Matrix.mul_apply,Matrix.one_apply,apply_ite]

theorem contraction_cast (A B M : Matrix (Fin m) (Fin m) ℚ) (eta : ℚ) :
    (contraction A B M eta:ℝ) =
      max (frobSq (1-(realMatrix A+(eta:ℝ) • 1)*realMatrix M))
      (frobSq (1-(realMatrix B+(eta:ℝ) • 1)*realMatrix M)) := by
  rw [contraction,Rat.cast_max,frobSq_cast,frobSq_cast,real_error,real_error]

def score (A B M : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (eta : ℚ) (k : Nat) : ℚ :=
  integrate (mul [1,-1] (energy A B d eta (solution A B M d eta k)))

theorem score_error (p q : List (Fin m → ℚ)) (M : Matrix (Fin m) (Fin m) ℚ)
    (eta : ℚ) (he : 0 < eta) (k : Nat) :
    |(score (moment p) (moment q) M (mean p-mean q) eta k:ℝ)-
      Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤
      (contraction (moment p) (moment q) M eta:ℝ)^k*
        (normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) := by
  apply energy_integral_error p q eta he
  intro r hr
  rw [solution_eval,contraction_cast,normSq_cast,moment_cast,moment_cast,difference_cast]
  exact residual_bound _ _ _ _ _ r hr k

#print axioms score_error
end Project.SpectralKL.MatrixPreconditioned
