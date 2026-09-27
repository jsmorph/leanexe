import Project.SpectralKL.DensePolynomial

namespace Project.SpectralKL.MatrixPolynomial
open Matrix Finset MeasureTheory intervalIntegral
open DensePolynomial
open scoped Matrix
variable {m : Nat}

def view {K : Type*} (v : Vector K m) : Fin m → K := fun i => v[i.val]
def store {K : Type*} (v : Fin m → K) : Vector K m := Vector.ofFn v
@[simp] theorem view_store {K : Type*} (v : Fin m → K) : view (store v) = v := by
  ext i; simp [view,store]

def sumTerms (f : Fin m → Poly) : Poly := DensePolynomial.sum (List.ofFn f)
@[simp] theorem eval_sumTerms (f : Fin m → Poly) (r : ℝ) :
    eval (sumTerms f) r = ∑ i, eval (f i) r := by
  simp [sumTerms,List.map_ofFn,List.sum_ofFn]

/-- Polynomial matrix S(r) = r A + (1-r) B. -/
def system (A B : Matrix (Fin m) (Fin m) ℚ) (i j : Fin m) : Poly :=
  [B i j, A i j-B i j]

/-- Exact rational polynomial iteration, with stored coordinates at every step. -/
def solution (A B : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (eta : ℚ) :
    Nat → Vector Poly m
  | 0 => store (fun _ => [])
  | k+1 =>
    let previous := solution A B d eta k
    store (fun i => scale (1/eta) (sub [d i]
      (sumTerms (fun j => mul (system A B i j) (view previous j)))))

def energy (A B : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (eta : ℚ)
    (x : Vector Poly m) : Poly :=
  sub (sub (scale 2 (sumTerms (fun i => scale (d i) (view x i))))
    (sumTerms (fun i => mul (view x i)
      (sumTerms (fun j => mul (system A B i j) (view x j))))))
    (scale eta (sumTerms (fun i => mul (view x i) (view x i))))

def score (A B : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (eta : ℚ) (k : Nat) : ℚ :=
  integrate (mul [1,-1] (energy A B d eta (solution A B d eta k)))

def realMatrix (A : Matrix (Fin m) (Fin m) ℚ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (A i j : ℝ)

theorem system_eval (A B : Matrix (Fin m) (Fin m) ℚ) (r : ℝ) (i j : Fin m) :
    eval (system A B i j) r = (r • realMatrix A+(1-r) • realMatrix B) i j := by
  simp [eval, system, realMatrix]
  ring

theorem solution_eval (A B : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    (eta : ℚ) (k : Nat) (r : ℝ) :
    (fun i => eval (view (solution A B d eta k) i) r) =
      MatrixIteration.iterate (r • realMatrix A+(1-r) • realMatrix B)
        (eta:ℝ) (Samples.realVec d) k := by
  induction k with
  | zero => ext i; simp [solution, MatrixIteration.iterate, eval]
  | succ k ih =>
    ext i
    simp only [solution, view_store, eval_scale, eval_sub, eval_sumTerms,
      eval_mul, system_eval, MatrixIteration.iterate, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, Rat.cast_div, Rat.cast_one]
    simp_rw [congrFun ih]
    simp [eval,Samples.realVec]

theorem energy_eval (A B : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ)
    (eta : ℚ) (x : Vector Poly m) (r : ℝ) :
    eval (energy A B d eta x) r =
      Residual.energy (r • realMatrix A+(1-r) • realMatrix B+(eta:ℝ) • 1)
        (Samples.realVec d) (fun i => eval (view x i) r) := by
  simp only [energy, eval_sub, eval_scale, eval_sumTerms, eval_mul,
    system_eval, Rat.cast_ofNat]
  simp only [Residual.energy, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul]
  simp only [dotProduct, Matrix.mulVec,
    Samples.realVec, Finset.mul_sum, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

#print axioms solution_eval
#print axioms energy_eval
end Project.SpectralKL.MatrixPolynomial
