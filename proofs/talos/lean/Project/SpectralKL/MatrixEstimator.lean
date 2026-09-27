import Project.SpectralKL.MatrixScore

namespace Project.SpectralKL.MatrixEstimator
open Matrix Finset Samples MatrixPolynomial
open scoped Matrix
variable {m : Nat}

abbrev StoredMatrix (m : Nat) := Vector (Vector ℚ m) m
def matrixView (a : StoredMatrix m) : Matrix (Fin m) (Fin m) ℚ :=
  fun i => view (view a i)
def matrixStore (a : Matrix (Fin m) (Fin m) ℚ) : StoredMatrix m :=
  store (fun i => store (a i))
@[simp] theorem matrixView_store (a : Matrix (Fin m) (Fin m) ℚ) :
    matrixView (matrixStore a) = a := by ext i j; simp [matrixView,matrixStore]

def sumRows (rows : List (Fin m → ℚ)) (acc : Vector ℚ m) : Vector ℚ m :=
  rows.foldl (fun a v => store (view a+v)) acc
theorem sumRows_eq (rows : List (Fin m → ℚ)) (acc : Vector ℚ m) :
    view (sumRows rows acc) = view acc+meanSum rows := by
  induction rows generalizing acc with
  | nil => simp [sumRows,meanSum]
  | cons v vs ih => simpa [sumRows,meanSum,add_assoc] using ih (store (view acc+v))

def gramRows (rows : List (Fin m → ℚ)) (acc : StoredMatrix m) : StoredMatrix m :=
  rows.foldl (fun a v => matrixStore (matrixView a+vecMulVec v v)) acc
theorem gramRows_eq (rows : List (Fin m → ℚ)) (acc : StoredMatrix m) :
    matrixView (gramRows rows acc) = matrixView acc+gramSum rows := by
  induction rows generalizing acc with
  | nil => simp [gramRows,gramSum]
  | cons v vs ih =>
    simpa [gramRows,gramSum,add_assoc] using ih (matrixStore (matrixView acc+vecMulVec v v))

def storedMean (rows : List (Fin m → ℚ)) : Vector ℚ m :=
  store ((1/(rows.length:ℚ)) • view (sumRows rows (store 0)))
def storedMoment (rows : List (Fin m → ℚ)) : StoredMatrix m :=
  matrixStore ((1/(rows.length:ℚ)) • matrixView (gramRows rows (matrixStore 0)))
@[simp] theorem storedMean_eq (rows : List (Fin m → ℚ)) :
    view (storedMean rows) = mean rows := by simp [storedMean,sumRows_eq,mean]
@[simp] theorem storedMoment_eq (rows : List (Fin m → ℚ)) :
    matrixView (storedMoment rows) = moment rows := by simp [storedMoment,gramRows_eq,moment]

/-- Round to a decimal grid so the reported score has a small, exact encoding. -/
def roundScore (x : ℚ) : Int := Int.floor (x*1000000000000)

theorem roundScore_error (x : ℚ) :
    |(roundScore x : ℝ)/1000000000000-(x:ℝ)| ≤ 1/1000000000000 := by
  have hl := Int.floor_le (x*1000000000000)
  have hu := Int.lt_floor_add_one (x*1000000000000)
  have hlR : (roundScore x:ℝ) ≤ (x:ℝ)*1000000000000 := by exact_mod_cast hl
  have huR : (x:ℝ)*1000000000000 < (roundScore x:ℝ)+1 := by exact_mod_cast hu
  apply abs_le.mpr
  constructor <;> linarith

/-- Input domain for the fixed twelve-step approximation. The Frobenius
condition concerns the input moments, not the computed score. -/
def Valid (p q : List (Fin m → ℚ)) (eta : ℚ) : Prop :=
  p ≠ [] ∧ q ≠ [] ∧ 0 < eta ∧
    frobSqQ (moment p)+frobSqQ (moment q) ≤ eta^2/4 ∧
    normSqQ (mean p-mean q) ≤ 32*eta

/-- Observations → exact sample moments → Richardson iteration on vector polynomials →
exact polynomial integral → rounded decimal score. No candidate score,
candidate solution vectors, or result acceptance checker is an input. -/
def compute (p q : List (Fin m → ℚ)) (eta : ℚ) : Option Int :=
  if p.isEmpty || q.isEmpty || eta ≤ 0 then none
  else
    let a := storedMoment p
    let b := storedMoment q
    let d := store (view (storedMean p)-view (storedMean q))
    if frobSqQ (matrixView a)+frobSqQ (matrixView b) > eta^2/4 ||
        normSqQ (view d) > 32*eta then none
    else some (roundScore (score (matrixView a) (matrixView b) (view d) eta 12))

theorem compute_eq (p q : List (Fin m → ℚ)) (eta : ℚ) (h : Valid p q eta) :
    compute p q eta = some (roundScore (sampleScore p q eta 12)) := by
  simp [compute, h.1,h.2.1,not_le.mpr h.2.2.1,not_lt.mpr h.2.2.2.1,
    not_lt.mpr h.2.2.2.2,sampleScore]

/-- Every input in the stated domain produces a score with absolute error
at most 10^-6 against the full sample-based inverse-matrix integral. -/
theorem compute_correct (p q : List (Fin m → ℚ)) (eta : ℚ) (h : Valid p q eta) :
    ∃ z, compute p q eta = some z ∧
      |(z:ℝ)/1000000000000-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ 1/1000000 := by
  refine ⟨roundScore (sampleScore p q eta 12),compute_eq p q eta h,?_⟩
  have he := sampleScore_error p q eta h.2.2.1 h.2.2.2.1 12
  have hr := roundScore_error (sampleScore p q eta 12)
  have hd : (normSqQ (mean p-mean q):ℝ) ≤ 32*(eta:ℝ) := by exact_mod_cast h.2.2.2.2
  have ep : (0:ℝ) < eta := by exact_mod_cast h.2.2.1
  have hb : (1/4:ℝ)^12 * (normSqQ (mean p-mean q):ℝ) / (2*(eta:ℝ)) ≤ 1/1048576 := by
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num
    linarith
  have ht := abs_sub_le ((roundScore (sampleScore p q eta 12):ℝ)/1000000000000)
    (sampleScore p q eta 12:ℝ) (Certificate.target (realRows p) (realRows q) (eta:ℝ))
  linarith

#print axioms compute_correct
end Project.SpectralKL.MatrixEstimator
