import Project.SpectralKL.MatrixPolynomial

namespace Project.SpectralKL.MatrixPolynomial
open Matrix Finset Samples MeasureTheory intervalIntegral DensePolynomial
open scoped Matrix
variable {m : Nat}

def frobSqQ (A : Matrix (Fin m) (Fin m) ℚ) : ℚ := ∑ i, ∑ j, (A i j)^2
def normSqQ (d : Fin m → ℚ) : ℚ := ∑ i, (d i)^2

theorem frobSq_cast (A : Matrix (Fin m) (Fin m) ℚ) :
    (frobSqQ A : ℝ) = MatrixIteration.frobSq (realMatrix A) := by
  simp [frobSqQ, MatrixIteration.frobSq, realMatrix]

theorem normSq_cast (d : Fin m → ℚ) :
    (normSqQ d : ℝ) = MatrixIteration.normSq (realVec d) := by
  simp [normSqQ, MatrixIteration.normSq, dotProduct, realVec, pow_two]

theorem gramSum_cast (p : List (Fin m → ℚ)) :
    realMatrix (gramSum p) = gramSum (realRows p) := by
  induction p with
  | nil => ext i j; simp [gramSum,realMatrix,realRows]
  | cons v p ih =>
    ext i j
    have h := congrFun (congrFun ih i) j
    simpa [gramSum,realMatrix,realRows,Matrix.vecMulVec] using
      congrArg (fun t => (v i:ℝ)*(v j:ℝ)+t) h

theorem moment_cast (p : List (Fin m → ℚ)) :
    realMatrix (moment p) = moment (realRows p) := by
  ext i j
  have h := congrFun (congrFun (gramSum_cast p) i) j
  simpa [moment,realMatrix,realRows] using
    congrArg (fun t => (1/(p.length:ℝ))*t) h

theorem difference_cast (p q : List (Fin m → ℚ)) :
    realVec (mean p-mean q) = mean (realRows p)-mean (realRows q) := by
  have h : realVec (mean p-mean q) = realVec (mean p)-realVec (mean q) := by
    ext i; simp [realVec]
  rw [h,mean_cast,mean_cast]

def sampleScore (p q : List (Fin m → ℚ)) (eta : ℚ) (k : Nat) : ℚ :=
  score (moment p) (moment q) (mean p-mean q) eta k

theorem sampleScore_error_with (p q : List (Fin m → ℚ)) (eta : ℚ)
    (he : 0 < eta)
    (rho : ℚ) (hrho : 0 ≤ rho)
    (hm : frobSqQ (moment p)+frobSqQ (moment q) ≤ rho*eta^2) (k : Nat) :
    |(sampleScore p q eta k : ℝ)-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤
      (rho:ℝ)^k * (normSqQ (mean p-mean q):ℝ) / (2*(eta:ℝ)) := by
  let A := moment (realRows p)
  let B := moment (realRows q)
  let d := mean (realRows p)-mean (realRows q)
  let x := solution (moment p) (moment q) (mean p-mean q) eta k
  let poly := mul [1,-1] (energy (moment p) (moment q) (mean p-mean q) eta x)
  let g := eval poly
  let E := (rho:ℝ)^k * MatrixIteration.normSq d / (eta:ℝ)
  have heR : (0:ℝ) < eta := by exact_mod_cast he
  have hmR : MatrixIteration.frobSq A+MatrixIteration.frobSq B ≤ (rho:ℝ)*(eta:ℝ)^2 := by
    dsimp only [A,B]
    rw [← moment_cast, ← moment_cast, ← frobSq_cast, ← frobSq_cast]
    exact_mod_cast hm
  have hg (r : ℝ) : g r = (1-r) * Residual.energy (Samples.system (realRows p) (realRows q) (eta:ℝ) r)
      d (MatrixIteration.iterate (r • A+(1-r) • B) (eta:ℝ) d k) := by
    dsimp [g,poly,x]
    rw [eval_mul,energy_eval,solution_eval,moment_cast,moment_cast,difference_cast]
    simp [eval,Samples.system,A,B,d,sub_eq_add_neg]
  have hpoint (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) :
      g r ≤ Certificate.integrand (realRows p) (realRows q) (eta:ℝ) r ∧
      Certificate.integrand (realRows p) (realRows q) (eta:ℝ) r ≤ g r+(1-r)*E := by
    have bounds := Residual.quadratic_bounds
      (Samples.system (realRows p) (realRows q) (eta:ℝ) r)
      (system_symmetric (realRows p) (realRows q) (eta:ℝ) r) (eta:ℝ)
      heR (system_coercive (realRows p) (realRows q) (eta:ℝ) r hr) d
      (MatrixIteration.iterate (r • A+(1-r) • B) (eta:ℝ) d k)
    have residualBound := MatrixIteration.residual_bound_with A B (eta:ℝ) heR (rho:ℝ) (by exact_mod_cast hrho) hmR d r hr k
    have hu : ((d-Samples.system (realRows p) (realRows q) (eta:ℝ) r *ᵥ
        MatrixIteration.iterate (r • A+(1-r) • B) (eta:ℝ) d k) ⬝ᵥ
        (d-Samples.system (realRows p) (realRows q) (eta:ℝ) r *ᵥ
        MatrixIteration.iterate (r • A+(1-r) • B) (eta:ℝ) d k))/(eta:ℝ) ≤ E := by
      apply div_le_div_of_nonneg_right _ heR.le
      exact residualBound
    have hw : 0 ≤ 1-r := sub_nonneg.mpr hr.2
    rw [hg]
    constructor
    · exact mul_le_mul_of_nonneg_left bounds.1 hw
    · have h := mul_le_mul_of_nonneg_left (bounds.2.trans (add_le_add le_rfl hu)) hw
      simpa only [mul_add,Certificate.integrand,d] using h
  have hf := Certificate.integrand_integrable (realRows p) (realRows q) (eta:ℝ) heR
    (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 1)
  have hgi : IntervalIntegrable g volume 0 1 := (eval_continuous poly).intervalIntegrable (0:ℝ) 1
  have hci : IntervalIntegrable (fun r : ℝ => (1-r)*E) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have hl := integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hgi hf (fun r hr => (hpoint r hr).1)
  have hu := integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hf (hgi.add hci) (fun r hr => (hpoint r hr).2)
  have hscore : (∫ r in (0:ℝ)..1, g r) = (sampleScore p q eta k : ℝ) :=
    (integrate_correct poly).symm
  rw [hscore] at hl
  rw [intervalIntegral.integral_add hgi hci,hscore,Certificate.weighted_const_integral] at hu
  change (sampleScore p q eta k : ℝ) ≤ Certificate.target _ _ _ at hl
  change Certificate.target _ _ _ ≤ (sampleScore p q eta k : ℝ)+_ at hu
  rw [abs_of_nonpos (sub_nonpos.mpr hl)]
  have hn : (normSqQ (mean p-mean q):ℝ) = MatrixIteration.normSq d := by
    rw [normSq_cast,difference_cast]
  rw [hn]
  dsimp [E] at hu
  norm_num at hu
  rw [show (rho:ℝ)^k * MatrixIteration.normSq d / (2*(eta:ℝ)) =
    (rho:ℝ)^k * MatrixIteration.normSq d / (eta:ℝ) * (1/2) by ring]
  linarith

theorem sampleScore_error (p q : List (Fin m → ℚ)) (eta : ℚ)
    (he : 0 < eta)
    (hm : frobSqQ (moment p)+frobSqQ (moment q) ≤ eta^2/4) (k : Nat) :
    |(sampleScore p q eta k : ℝ)-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤
      (1/4:ℝ)^k * (normSqQ (mean p-mean q):ℝ) / (2*(eta:ℝ)) := by
  simpa using sampleScore_error_with p q eta he (1/4) (by norm_num) (by linarith) k

#print axioms sampleScore_error_with
#print axioms sampleScore_error
end Project.SpectralKL.MatrixPolynomial
