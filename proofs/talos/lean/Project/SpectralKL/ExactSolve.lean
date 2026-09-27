import Project.SpectralKL.MatrixEstimator

namespace Project.SpectralKL.ExactSolve
open Matrix Finset MatrixPolynomial MatrixEstimator
open scoped Matrix

/-- Positivity of the quadratic form. Symmetry is not needed by the elimination proof. -/
def Positive {m : Nat} (A : Matrix (Fin m) (Fin m) ℚ) : Prop :=
  ∀ v : Fin m → ℚ, v ≠ 0 → 0 < v ⬝ᵥ (A *ᵥ v)

def schur {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => A i.succ j.succ-A i.succ 0*A 0 j.succ/A 0 0

def reducedRight {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (b : Fin (n+1) → ℚ) : Fin n → ℚ := fun i => b i.succ-A i.succ 0*b 0/A 0 0

def complete {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (b : Fin (n+1) → ℚ) (y : Fin n → ℚ) : Fin (n+1) → ℚ :=
  Fin.cons ((b 0-∑ j, A 0 j.succ*y j)/A 0 0) y

theorem first_row {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (b : Fin (n+1) → ℚ) (y : Fin n → ℚ) (ha : A 0 0 ≠ 0) :
    (A *ᵥ complete A b y) 0 = b 0 := by
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,complete,Fin.cons_zero,Fin.cons_succ]
  field_simp
  ring

theorem schur_action {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (y : Fin n → ℚ) (i : Fin n) :
    (schur A *ᵥ y) i = (∑ j, A i.succ j.succ*y j)-(A i.succ 0/A 0 0)*(∑ j, A 0 j.succ*y j) := by
  simp only [schur,Matrix.mulVec,dotProduct,Matrix.of_apply,sub_mul,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem remaining_rows {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (b : Fin (n+1) → ℚ) (y : Fin n → ℚ) (i : Fin n) :
    (A *ᵥ complete A b y) i.succ = (schur A *ᵥ y) i+A i.succ 0*b 0/A 0 0 := by
  rw [schur_action]
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,complete,Fin.cons_zero,Fin.cons_succ]
  ring

theorem solve_lift {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (b : Fin (n+1) → ℚ) (y : Fin n → ℚ) (ha : A 0 0 ≠ 0)
    (hy : schur A *ᵥ y = reducedRight A b) : A *ᵥ complete A b y = b := by
  ext i
  refine Fin.cases (first_row A b y ha) (fun j => ?_) i
  rw [remaining_rows,hy,reducedRight]
  ring

theorem positive_pivot {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (h : Positive A) :
    0 < A 0 0 := by
  let e : Fin (n+1) → ℚ := Fin.cons 1 0
  have he : e ≠ 0 := by
    intro hz
    have hz0 := congrFun hz 0
    norm_num [e] at hz0
  have hp := h e he
  simpa [e,dotProduct,Matrix.mulVec,Fin.sum_univ_succ] using hp

theorem positive_schur {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (h : Positive A) :
    Positive (schur A) := by
  intro y hy
  have ha := positive_pivot A h
  have hx : complete A 0 y ≠ 0 := by
    intro hz
    apply hy
    ext i
    have hi := congrFun hz i.succ
    simpa [complete] using hi
  have hp := h (complete A 0 y) hx
  have he : (complete A 0 y) ⬝ᵥ (A *ᵥ complete A 0 y) = y ⬝ᵥ (schur A *ᵥ y) := by
    rw [dotProduct,Fin.sum_univ_succ,first_row A 0 y ha.ne']
    simp only [remaining_rows,Pi.zero_apply,mul_zero,zero_add,zero_div,add_zero]
    simp only [complete,Fin.cons_succ]
    rfl
  rwa [he] at hp

/-- Exact rational elimination with stored Schur complements and right-hand sides. -/
def solve : (m : Nat) → StoredMatrix m → Vector ℚ m → Vector ℚ m
  | 0,_,_ => store (fun i => Fin.elim0 i)
  | n+1,a,b =>
    let A := matrixView a
    let rhs := view b
    let s := matrixStore (schur A)
    let c := store (reducedRight A rhs)
    let y := solve n s c
    store (complete A rhs (view y))

theorem solve_correct (m : Nat) (a : StoredMatrix m) (b : Vector ℚ m)
    (h : Positive (matrixView a)) : matrixView a *ᵥ view (solve m a b) = view b := by
  induction m with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    have ha := positive_pivot (matrixView a) h
    have hs := positive_schur (matrixView a) h
    have hy := ih (matrixStore (schur (matrixView a))) (store (reducedRight (matrixView a) (view b)))
      (by simpa using hs)
    simp only [matrixView_store,view_store] at hy
    simp only [solve,view_store]
    exact solve_lift (matrixView a) (view b) _ ha.ne' hy

/-- The pivots and border entries needed for forward elimination and back
substitution. Factoring once allows all inverse columns to share the work. -/
inductive Factors : Nat → Type
  | empty : Factors 0
  | step {n : Nat} (pivot : ℚ) (row col : Vector ℚ n) (tail : Factors n) : Factors (n+1)

def factor : (m : Nat) → StoredMatrix m → Factors m
  | 0,_ => .empty
  | n+1,a =>
    let A := matrixView a
    .step (A 0 0) (store (fun j => A 0 j.succ)) (store (fun i => A i.succ 0))
      (factor n (matrixStore (schur A)))

def applyFactors : (m : Nat) → Factors m → Vector ℚ m → Vector ℚ m
  | 0,.empty,_ => store (fun i => Fin.elim0 i)
  | n+1,.step pivot row col tail,b =>
    let c := store (fun i => view b i.succ-view col i*view b 0/pivot)
    let y := applyFactors n tail c
    store (Fin.cons ((view b 0-∑ j, view row j*view y j)/pivot) (view y))

theorem applyFactors_eq (m : Nat) (a : StoredMatrix m) (b : Vector ℚ m) :
    applyFactors m (factor m a) b = solve m a b := by
  induction m with
  | zero => rfl
  | succ n ih =>
    simp only [factor,applyFactors,view_store]
    rw [ih]
    rfl

theorem applyFactors_correct (m : Nat) (a : StoredMatrix m) (b : Vector ℚ m)
    (h : Positive (matrixView a)) :
    matrixView a *ᵥ view (applyFactors m (factor m a) b) = view b := by
  rw [applyFactors_eq]
  exact solve_correct m a b h

#print axioms solve_correct
#print axioms applyFactors_correct
end Project.SpectralKL.ExactSolve
