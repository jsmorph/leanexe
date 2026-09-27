import Project.SpectralKL.MatrixDamped

namespace Project.SpectralKL.MatrixDamped
open Matrix Finset Samples MatrixPolynomial DensePolynomial MeasureTheory intervalIntegral
open scoped Matrix
variable {m : Nat}

/-- Executable damped iteration on stored vectors of exact rational polynomials. -/
def solution (A B : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (eta a : ℚ) :
    Nat → Vector Poly m
  | 0 => store (fun _ => [])
  | k+1 =>
    let previous := solution A B d eta a k
    store (fun i => add (view previous i) (scale a (sub [d i]
      (add (sumTerms (fun j => mul (MatrixPolynomial.system A B i j) (view previous j)))
        (scale eta (view previous i))))))

theorem solution_eval (A B : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    (eta a : ℚ) (k : Nat) (r : ℝ) :
    (fun i => eval (view (solution A B d eta a k) i) r) =
      iterate (r • realMatrix A+(1-r) • realMatrix B+(eta:ℝ) • 1)
        (a:ℝ) (realVec d) k := by
  induction k with
  | zero => ext i; simp [solution,iterate,eval]
  | succ k ih =>
    ext i
    simp only [solution,view_store,eval_add,eval_scale,eval_sub,eval_sumTerms,eval_mul,
      system_eval,iterate,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
      Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Matrix.mulVec,dotProduct]
    simp_rw [congrFun ih]
    simp [eval,realVec,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]

def upperSqQ (A B : Matrix (Fin m) (Fin m) ℚ) (eta : ℚ) : ℚ :=
  2*(eta^2+frobSqQ A+frobSqQ B)

theorem upperSqQ_cast (p q : List (Fin m → ℚ)) (eta : ℚ) :
    (upperSqQ (moment p) (moment q) eta : ℝ) = upperSq (realRows p) (realRows q) (eta:ℝ) := by
  simp only [upperSqQ,upperSq,Rat.cast_mul,Rat.cast_add,Rat.cast_pow,Rat.cast_ofNat,
    frobSq_cast,moment_cast]

def score (A B : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (eta : ℚ) (k : Nat) : ℚ :=
  integrate (mul [1,-1] (energy A B d eta (solution A B d eta (eta/upperSqQ A B eta) k)))

def sampleScore (p q : List (Fin m → ℚ)) (eta : ℚ) (k : Nat) : ℚ :=
  score (moment p) (moment q) (mean p-mean q) eta k

def contraction (p q : List (Fin m → ℚ)) (eta : ℚ) : ℚ :=
  1-eta^2/upperSqQ (moment p) (moment q) eta

theorem sampleScore_error (p q : List (Fin m → ℚ)) (eta : ℚ)
    (he : 0 < eta) (k : Nat) :
    |(sampleScore p q eta k : ℝ)-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤
      (contraction p q eta:ℝ)^k * (normSqQ (mean p-mean q):ℝ) / (2*(eta:ℝ)) := by
  let d := mean (realRows p)-mean (realRows q)
  let U := upperSq (realRows p) (realRows q) (eta:ℝ)
  let rho := 1-(eta:ℝ)^2/U
  let x := solution (moment p) (moment q) (mean p-mean q) eta
    (eta/upperSqQ (moment p) (moment q) eta) k
  let poly := mul [1,-1] (energy (moment p) (moment q) (mean p-mean q) eta x)
  let g := eval poly
  let E := rho^k * MatrixIteration.normSq d / (eta:ℝ)
  have heR : (0:ℝ) < eta := by exact_mod_cast he
  have hg (r : ℝ) : g r = (1-r) * Residual.energy (Samples.system (realRows p) (realRows q) (eta:ℝ) r)
      d (iterate (Samples.system (realRows p) (realRows q) (eta:ℝ) r) ((eta:ℝ)/U) d k) := by
    dsimp [g,poly,x]
    rw [eval_mul,energy_eval,solution_eval,moment_cast,moment_cast,difference_cast]
    simp [eval,Samples.system,U,d,sub_eq_add_neg,upperSqQ_cast]
  have hpoint (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) 1) :
      g r ≤ Certificate.integrand (realRows p) (realRows q) (eta:ℝ) r ∧
      Certificate.integrand (realRows p) (realRows q) (eta:ℝ) r ≤ g r+(1-r)*E := by
    have bounds := Residual.quadratic_bounds
      (Samples.system (realRows p) (realRows q) (eta:ℝ) r)
      (system_symmetric (realRows p) (realRows q) (eta:ℝ) r) (eta:ℝ)
      heR (system_coercive (realRows p) (realRows q) (eta:ℝ) r hr) d
      (iterate (Samples.system (realRows p) (realRows q) (eta:ℝ) r) ((eta:ℝ)/U) d k)
    have rb := residual_bound (realRows p) (realRows q) (eta:ℝ) heR d r hr k
    have hu : ((d-Samples.system (realRows p) (realRows q) (eta:ℝ) r *ᵥ
        iterate (Samples.system (realRows p) (realRows q) (eta:ℝ) r) ((eta:ℝ)/U) d k) ⬝ᵥ
        (d-Samples.system (realRows p) (realRows q) (eta:ℝ) r *ᵥ
        iterate (Samples.system (realRows p) (realRows q) (eta:ℝ) r) ((eta:ℝ)/U) d k))/(eta:ℝ) ≤ E :=
      div_le_div_of_nonneg_right rb heR.le
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
  have hc : (contraction p q eta:ℝ) = rho := by
    simp only [contraction,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_pow,upperSqQ_cast,rho,U]
  rw [hn,hc]
  dsimp [E] at hu
  norm_num at hu
  rw [show rho^k * MatrixIteration.normSq d / (2*(eta:ℝ)) =
    rho^k * MatrixIteration.normSq d / (eta:ℝ) * (1/2) by ring]
  linarith

#print axioms solution_eval
#print axioms sampleScore_error
end Project.SpectralKL.MatrixDamped
