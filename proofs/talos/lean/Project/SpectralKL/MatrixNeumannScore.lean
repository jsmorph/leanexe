import Project.SpectralKL.MatrixNeumann

namespace Project.SpectralKL.MatrixNeumann
open Matrix Finset MatrixPolynomial MatrixEstimator Samples DensePolynomial MeasureTheory intervalIntegral
open scoped Matrix
variable {m : Nat}

def centeredOperator (A B M : Matrix (Fin m) (Fin m) ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  -(M*((1/2:ℚ) • (A-B)))

theorem centeredOperator_cast (A B M : Matrix (Fin m) (Fin m) ℚ) :
    realMatrix (centeredOperator A B M) =
      -(realMatrix M*((1/2:ℝ) • (realMatrix A-realMatrix B))) := by
  ext i j
  simp [centeredOperator,realMatrix,Matrix.mul_apply]

theorem real_mul (A B : Matrix (Fin m) (Fin m) ℚ) :
    realMatrix (A*B) = realMatrix A*realMatrix B := by
  ext i j
  simp [realMatrix,Matrix.mul_apply]

theorem real_one : realMatrix (1 : Matrix (Fin m) (Fin m) ℚ) = 1 := by
  ext i j
  by_cases h : i=j <;> simp [realMatrix,Matrix.one_apply,h]

def score (A B M : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (k : Nat) : ℚ :=
  scoreFrom (matrixStore (centeredOperator A B M)) (store d) (store (M *ᵥ d)) [1] (2*k)

theorem score_integral (A B M : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (k : Nat) :
    (score A B M d k:ℝ) = ∫ r in (0:ℝ)..1, (1-r)*
      (realVec d ⬝ᵥ geometric (realMatrix (centeredOperator A B M))
        (realVec (M *ᵥ d)) (2*k) (2*r-1)) := by
  rw [score,scoreFrom_integral]
  simp only [matrixView_store,view_store]
  apply intervalIntegral.integral_congr
  intro r _
  simp [eval]

theorem score_error (p q : List (Fin m → ℚ)) (M : Matrix (Fin m) (Fin m) ℚ)
    (eta : ℚ) (he : 0 < eta)
    (hM : ExactSolve.midpoint (moment p) (moment q) eta*M=1) (k : Nat) :
    |(score (moment p) (moment q) M (mean p-mean q) k:ℝ)-
      Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤
      (MatrixPreconditioned.contraction (moment p) (moment q) M eta:ℝ)^k*
        (normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) := by
  let A := moment (realRows p)
  let B := moment (realRows q)
  let d := mean (realRows p)-mean (realRows q)
  let T := realMatrix (centeredOperator (moment p) (moment q) M)
  let u := realVec (M *ᵥ (mean p-mean q))
  let y := fun r : ℝ => geometric T u (2*k) (2*r-1)
  let rho : ℝ := (MatrixPreconditioned.contraction (moment p) (moment q) M eta:ℝ)
  let E := rho^k*MatrixIteration.normSq d/(eta:ℝ)
  let g := fun r : ℝ => (1-r)*(d ⬝ᵥ y r)
  have heR : (0:ℝ)<eta := by exact_mod_cast he
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    rw [MatrixPreconditioned.contraction_cast]
    unfold MatrixIteration.frobSq
    positivity
  have hleft : realMatrix M*((1/2:ℝ) • A+(1/2:ℝ) • B+(eta:ℝ) • 1)=1 := by
    have hl : M*ExactSolve.midpoint (moment p) (moment q) eta=1 := mul_eq_one_comm.mp hM
    have hh := congrArg realMatrix hl
    rw [real_mul,ExactSolve.midpoint_cast,real_one] at hh
    norm_num [Samples.system] at hh
    exact hh
  have hy (r : ℝ) : y r = MatrixPreconditioned.iterate
      (Samples.system (realRows p) (realRows q) (eta:ℝ) r) (realMatrix M) d (2*k) := by
    dsimp only [y,T,u]
    rw [centeredOperator_cast,mulVec_cast,moment_cast,moment_cast,difference_cast]
    exact geometric_iterate A B (realMatrix M) (eta:ℝ) r hleft d (2*k)
  have hpoint (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) :
      g r-(1-r)*E ≤ Certificate.integrand (realRows p) (realRows q) (eta:ℝ) r ∧
      Certificate.integrand (realRows p) (realRows q) (eta:ℝ) r ≤ g r+(1-r)*E := by
    have hres := MatrixPreconditioned.residual_bound A B (realMatrix M) (eta:ℝ) d r hr (2*k)
    have hp : rho^(2*k) = (rho^k)^2 := by rw [Nat.mul_comm 2 k,pow_mul]
    have hrb : MatrixIteration.normSq (d-Samples.system (realRows p) (realRows q) (eta:ℝ) r *ᵥ y r) ≤
        (rho^k)^2*MatrixIteration.normSq d := by
      rw [hy,← hp]
      dsimp [rho]
      rw [MatrixPreconditioned.contraction_cast,moment_cast,moment_cast]
      exact hres
    have hl := MatrixPreconditioned.linear_error
      (Samples.system (realRows p) (realRows q) (eta:ℝ) r) d (y r) (eta:ℝ) heR
      (system_symmetric _ _ _ _) (system_coercive _ _ _ _ hr) (rho^k) (pow_nonneg hrho _) hrb
    have hb := abs_le.mp hl
    have hw : 0 ≤ 1-r := sub_nonneg.mpr hr.2
    have h1 := mul_le_mul_of_nonneg_left hb.1 hw
    have h2 := mul_le_mul_of_nonneg_left hb.2 hw
    dsimp only [g,Certificate.integrand,E,d] at *
    constructor <;> nlinarith
  have hgc : Continuous g := by
    have hgy : Continuous y := (geometric_continuous T u (2*k)).comp (by fun_prop)
    exact (continuous_const.sub continuous_id).mul (continuous_const.dotProduct hgy)
  have hgi : IntervalIntegrable g volume 0 1 := hgc.intervalIntegrable _ _
  have hci : IntervalIntegrable (fun r : ℝ => (1-r)*E) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hf := Certificate.integrand_integrable (realRows p) (realRows q) (eta:ℝ) heR
    (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤1)
  have hl := integral_mono_on (by norm_num : (0:ℝ)≤1) (hgi.sub hci) hf (fun r hr => (hpoint r hr).1)
  have hu := integral_mono_on (by norm_num : (0:ℝ)≤1) hf (hgi.add hci) (fun r hr => (hpoint r hr).2)
  have hscore : (∫ r in (0:ℝ)..1,g r) = (score (moment p) (moment q) M (mean p-mean q) k:ℝ) := by
    rw [score_integral,difference_cast]
  rw [intervalIntegral.integral_sub hgi hci,hscore,Certificate.weighted_const_integral] at hl
  rw [intervalIntegral.integral_add hgi hci,hscore,Certificate.weighted_const_integral] at hu
  change _ ≤ Certificate.target _ _ _ at hl
  change Certificate.target _ _ _ ≤ _ at hu
  have hn : (normSqQ (mean p-mean q):ℝ) = MatrixIteration.normSq d := by rw [normSq_cast,difference_cast]
  rw [hn]
  change |_ - _| ≤ rho^k*MatrixIteration.normSq d/(2*(eta:ℝ))
  rw [show rho^k*MatrixIteration.normSq d/(2*(eta:ℝ)) = E*(1/2) by dsimp [E]; ring]
  norm_num at hl hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

#print axioms score_error
end Project.SpectralKL.MatrixNeumann
