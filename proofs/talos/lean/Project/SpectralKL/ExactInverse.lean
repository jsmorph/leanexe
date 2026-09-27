import Project.SpectralKL.ExactSolve

namespace Project.SpectralKL.ExactSolve
open Matrix MatrixPolynomial MatrixEstimator Samples
open scoped Matrix
variable {m : Nat}

/-- Store the solves of all coordinate vectors as the columns of the inverse. -/
def inverse (a : StoredMatrix m) : StoredMatrix m :=
  let factors := factor m a
  let columns := store (fun j : Fin m => applyFactors m factors (store (fun i => if i=j then 1 else 0)))
  matrixStore (Matrix.of fun i j => view (view columns j) i)

theorem inverse_correct (a : StoredMatrix m) (h : Positive (matrixView a)) :
    matrixView a * matrixView (inverse a) = 1 := by
  ext i j
  have hs := congrFun (applyFactors_correct m a (store (fun i => if i=j then 1 else 0)) h) i
  simpa [inverse,Matrix.mul_apply,Matrix.mulVec,dotProduct,Matrix.one_apply] using hs

def midpoint (A B : Matrix (Fin m) (Fin m) ℚ) (eta : ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  (1/2:ℚ) • A+(1/2:ℚ) • B+eta • 1

theorem midpoint_cast (p q : List (Fin m → ℚ)) (eta : ℚ) :
    realMatrix (midpoint (moment p) (moment q) eta) =
      Samples.system (realRows p) (realRows q) (eta:ℝ) (1/2) := by
  have hA := moment_cast p
  have hB := moment_cast q
  ext i j
  have hAi := congrFun (congrFun hA i) j
  have hBi := congrFun (congrFun hB i) j
  simp only [realMatrix] at hAi hBi
  have hone : (((1 : Matrix (Fin m) (Fin m) ℚ) i j):ℝ) =
      (1 : Matrix (Fin m) (Fin m) ℝ) i j := by
    by_cases hij : i=j <;> simp [Matrix.one_apply,hij]
  simp only [realMatrix,midpoint,Samples.system,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,hAi,hBi,hone]
  congr 2
  norm_num

theorem midpoint_positive (p q : List (Fin m → ℚ)) (eta : ℚ) (he : 0 < eta) :
    Positive (midpoint (moment p) (moment q) eta) := by
  intro v hv
  have hvR : realVec v ≠ 0 := by
    intro hz
    apply hv
    ext i
    have hi := congrFun hz i
    simpa [realVec] using hi
  have hn : 0 < realVec v ⬝ᵥ realVec v := lt_of_le_of_ne (Residual.self_nonneg _)
    (Ne.symm (fun hz => hvR (dotProduct_self_eq_zero.mp hz)))
  have hc := system_coercive (realRows p) (realRows q) (eta:ℝ) (1/2)
    (by norm_num) (realVec v)
  have hp := (mul_pos (show (0:ℝ)<eta by exact_mod_cast he) hn).trans_le hc
  rw [← midpoint_cast] at hp
  have hcast : ((v ⬝ᵥ (midpoint (moment p) (moment q) eta *ᵥ v):ℚ):ℝ) =
      realVec v ⬝ᵥ (realMatrix (midpoint (moment p) (moment q) eta) *ᵥ realVec v) := by
    simp [dotProduct,Matrix.mulVec,realMatrix,realVec]
  rw [← hcast] at hp
  exact_mod_cast hp

def preconditioner (A B : Matrix (Fin m) (Fin m) ℚ) (eta : ℚ) : StoredMatrix m :=
  inverse (matrixStore (midpoint A B eta))

theorem preconditioner_correct (p q : List (Fin m → ℚ)) (eta : ℚ) (he : 0 < eta) :
    midpoint (moment p) (moment q) eta *
      matrixView (preconditioner (moment p) (moment q) eta) = 1 := by
  simpa only [preconditioner,matrixView_store] using
    inverse_correct (matrixStore _) (by simpa using midpoint_positive p q eta he)

#print axioms preconditioner_correct
end Project.SpectralKL.ExactSolve
