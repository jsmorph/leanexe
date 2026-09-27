import Project.SpectralKL.MatrixLinearBound

namespace Project.SpectralKL.MatrixNeumann
open Matrix Finset MatrixPolynomial MatrixEstimator Samples DensePolynomial MeasureTheory intervalIntegral
open scoped Matrix
variable {m : Nat}

/-- Centered finite geometric series; the executable score below streams its
coefficient vectors instead of constructing a vector of long polynomials. -/
noncomputable def geometric (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) :
    Nat → ℝ → Fin m → ℝ
  | 0,_ => 0
  | k+1,t => u+t • geometric T (T *ᵥ u) k t

theorem geometric_mulVec (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) (k : Nat) (t : ℝ) :
    geometric T (T *ᵥ u) k t = T *ᵥ geometric T u k t := by
  induction k generalizing u with
  | zero => simp [geometric]
  | succ k ih => simp only [geometric,Matrix.mulVec_add,Matrix.mulVec_smul,ih]

theorem geometric_continuous (T : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) (k : Nat) :
    Continuous (geometric T u k) := by
  induction k generalizing u with
  | zero => simp only [geometric]; fun_prop
  | succ k ih => exact continuous_const.add (continuous_id.smul (ih _))

theorem midpoint_decomposition (A B : Matrix (Fin m) (Fin m) ℝ) (eta r : ℝ) :
    r • A+(1-r) • B+eta • 1 =
      ((1/2:ℝ) • A+(1/2:ℝ) • B+eta • 1)+(2*r-1) • ((1/2:ℝ) • (A-B)) := by
  module

theorem centered_step (A B M : Matrix (Fin m) (Fin m) ℝ) (eta r : ℝ)
    (hM : M*((1/2:ℝ) • A+(1/2:ℝ) • B+eta • 1)=1) (d x : Fin m → ℝ) :
    x+M *ᵥ (d-(r • A+(1-r) • B+eta • 1) *ᵥ x) =
      M *ᵥ d+(2*r-1) • ((-(M*((1/2:ℝ) • (A-B)))) *ᵥ x) := by
  rw [midpoint_decomposition,Matrix.mulVec_sub,Matrix.mulVec_mulVec,
    Matrix.mul_add,Matrix.mul_smul,hM,Matrix.add_mulVec,Matrix.one_mulVec,
    Matrix.smul_mulVec,Matrix.neg_mulVec]
  module

theorem geometric_iterate (A B M : Matrix (Fin m) (Fin m) ℝ) (eta r : ℝ)
    (hM : M*((1/2:ℝ) • A+(1/2:ℝ) • B+eta • 1)=1) (d : Fin m → ℝ) (k : Nat) :
    geometric (-(M*((1/2:ℝ) • (A-B)))) (M *ᵥ d) k (2*r-1) =
      MatrixPreconditioned.iterate (r • A+(1-r) • B+eta • 1) M d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [geometric,geometric_mulVec,ih,MatrixPreconditioned.iterate,centered_step A B M eta r hM]

theorem mulVec_cast (A : Matrix (Fin m) (Fin m) ℚ) (v : Fin m → ℚ) :
    realVec (A *ᵥ v) = realMatrix A *ᵥ realVec v := by
  ext i
  simp [realVec,realMatrix,Matrix.mulVec,dotProduct]

/-- Stream the centered monomial and its coefficient vector. The small scalar
polynomial supplies its exact integration weight; no vector polynomial or
quadratic product of vector polynomials is constructed. -/
def scoreFrom (T : StoredMatrix m) (d : Vector ℚ m) : Vector ℚ m → Poly → Nat → ℚ
  | _,_,0 => 0
  | v,p,k+1 =>
    integrate (mul [1,-1] p)*(view d ⬝ᵥ view v)+
      scoreFrom T d (store (matrixView T *ᵥ view v)) (mul [-1,2] p) k

theorem scoreFrom_integral (T : StoredMatrix m) (d v : Vector ℚ m) (p : Poly) (k : Nat) :
    (scoreFrom T d v p k:ℝ) =
      ∫ r in (0:ℝ)..1, (1-r)*eval p r*
        (realVec (view d) ⬝ᵥ geometric (realMatrix (matrixView T)) (realVec (view v)) k (2*r-1)) := by
  induction k generalizing v p with
  | zero => simp [scoreFrom,geometric]
  | succ k ih =>
    have hc : Continuous (fun r : ℝ => realVec (view d) ⬝ᵥ
        geometric (realMatrix (matrixView T))
          (realMatrix (matrixView T) *ᵥ realVec (view v)) k (2*r-1)) := by
      have hg := (geometric_continuous (realMatrix (matrixView T))
        (realMatrix (matrixView T) *ᵥ realVec (view v)) k).comp
          (by fun_prop : Continuous (fun r : ℝ => 2*r-1))
      exact continuous_const.dotProduct hg
    have h1 : IntervalIntegrable (fun r : ℝ => (1-r)*eval p r*(realVec (view d) ⬝ᵥ realVec (view v))) volume 0 1 :=
      (continuous_const.sub continuous_id |>.mul (eval_continuous p) |>.mul continuous_const).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun r : ℝ => (1-r)*eval (mul [-1,2] p) r*
        (realVec (view d) ⬝ᵥ geometric (realMatrix (matrixView T))
          (realMatrix (matrixView T) *ᵥ realVec (view v)) k (2*r-1))) volume 0 1 :=
      ((continuous_const.sub continuous_id).mul (eval_continuous _) |>.mul hc).intervalIntegrable _ _
    have he : (fun r : ℝ => (1-r)*eval p r*(realVec (view d) ⬝ᵥ
        geometric (realMatrix (matrixView T)) (realVec (view v)) (k+1) (2*r-1))) =
      (fun r : ℝ => (1-r)*eval p r*(realVec (view d) ⬝ᵥ realVec (view v))+
        (1-r)*eval (mul [-1,2] p) r*(realVec (view d) ⬝ᵥ
          geometric (realMatrix (matrixView T)) (realMatrix (matrixView T) *ᵥ realVec (view v)) k (2*r-1))) := by
      ext r
      simp only [geometric,dotProduct_add,dotProduct_smul,smul_eq_mul,eval_mul]
      simp [eval]
      ring
    rw [he,intervalIntegral.integral_add h1 h2,scoreFrom,Rat.cast_add,Rat.cast_mul,
      ih,view_store,mulVec_cast,dot_cast,integrate_correct]
    congr 1
    rw [intervalIntegral.integral_mul_const]
    congr 1
    apply intervalIntegral.integral_congr
    intro r _
    simp [eval,sub_eq_add_neg]

#print axioms scoreFrom_integral
end Project.SpectralKL.MatrixNeumann
