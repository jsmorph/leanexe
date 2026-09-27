import Project.SpectralKL.MatrixNeumannScore
import Project.SpectralKL.MatrixAuto

namespace Project.SpectralKL.MatrixAccelerated
open MatrixPolynomial MatrixEstimator Samples
variable {m : Nat}

def baseContraction (A B : Matrix (Fin m) (Fin m) ℚ) (eta : ℚ) : ℚ :=
  min ((frobSqQ A+frobSqQ B)/eta^2) (1-eta^2/MatrixDamped.upperSqQ A B eta)

def selectedContraction (p q : List (Fin m → ℚ)) (M : Matrix (Fin m) (Fin m) ℚ)
    (eta : ℚ) : ℚ :=
  min (baseContraction (moment p) (moment q) eta)
    (MatrixPreconditioned.contraction (moment p) (moment q) M eta)

def selectedScore (A B M : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (eta : ℚ)
    (k : Nat) : ℚ :=
  if MatrixPreconditioned.contraction A B M eta < baseContraction A B eta then
    MatrixNeumann.score A B M d k
  else MatrixGeneral.selectedScore A B d eta k

theorem contraction_range (p q : List (Fin m → ℚ)) (M : Matrix (Fin m) (Fin m) ℚ)
    (eta : ℚ) (he : 0 < eta) :
    0 ≤ selectedContraction p q M eta ∧ selectedContraction p q M eta < 1 := by
  have hb := MatrixGeneral.selectedContraction_range p q eta he
  have hp : 0 ≤ MatrixPreconditioned.contraction (moment p) (moment q) M eta := by
    unfold MatrixPreconditioned.contraction frobSqQ
    positivity
  exact ⟨le_min hb.1 hp,(min_le_left _ _).trans_lt hb.2⟩

theorem selectedScore_error (p q : List (Fin m → ℚ)) (M : Matrix (Fin m) (Fin m) ℚ)
    (eta : ℚ) (he : 0 < eta)
    (hM : ExactSolve.midpoint (moment p) (moment q) eta*M=1) (k : Nat) :
    |(selectedScore (moment p) (moment q) M (mean p-mean q) eta k:ℝ)-
      Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤
      (selectedContraction p q M eta:ℝ)^k * (normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) := by
  unfold selectedScore
  split
  · rename_i h
    simpa only [selectedContraction,min_eq_right h.le] using
      MatrixNeumann.score_error p q M eta he hM k
  · rename_i h
    have hs := MatrixGeneral.selectedSampleScore_error p q eta he k
    change |(MatrixGeneral.selectedScore (moment p) (moment q) (mean p-mean q) eta k:ℝ)-_| ≤
      (baseContraction (moment p) (moment q) eta:ℝ)^k*(normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) at hs
    simpa only [selectedContraction,min_eq_left (le_of_not_gt h)] using hs

/-- The matrix inverse and moment matrices are stored and reused by the exact
polynomial iteration. All three methods have proved error bounds. -/
def computeMoments (a b : StoredMatrix m) (d : Vector ℚ m) (eta : ℚ) : Int × Nat :=
  let M := ExactSolve.preconditioner (matrixView a) (matrixView b) eta
  let base := baseContraction (matrixView a) (matrixView b) eta
  let pre := MatrixPreconditioned.contraction (matrixView a) (matrixView b) (matrixView M) eta
  let rho := min base pre
  let k := GeometricBudget.select rho (normSqQ (view d)/(2*eta)) MatrixEstimator.polynomialBudget
  (roundScore (selectedScore (matrixView a) (matrixView b) (matrixView M) (view d) eta k),
    if pre<base then 2*k else k)

def compute (p q : List (Fin m → ℚ)) (eta : ℚ) : Option (Int × Nat) :=
  if p.isEmpty || q.isEmpty || eta ≤ 0 then none
  else
    let a := storedMoment p
    let b := storedMoment q
    let d := store (view (storedMean p)-view (storedMean q))
    some (computeMoments a b d eta)

theorem compute_eq (p q : List (Fin m → ℚ)) (eta : ℚ) (h : MatrixGeneral.Valid p q eta) :
    compute p q eta =
      let M := matrixView (ExactSolve.preconditioner (moment p) (moment q) eta)
      let k := GeometricBudget.select (selectedContraction p q M eta)
        (MatrixEstimator.initialBound p q eta) MatrixEstimator.polynomialBudget
      some (roundScore (selectedScore (moment p) (moment q) M (mean p-mean q) eta k),
        if MatrixPreconditioned.contraction (moment p) (moment q) M eta <
          baseContraction (moment p) (moment q) eta then 2*k else k) := by
  simp [compute,computeMoments,h.1,h.2.1,not_le.mpr h.2.2,selectedContraction,MatrixEstimator.initialBound]

theorem compute_correct (p q : List (Fin m → ℚ)) (eta : ℚ) (h : MatrixGeneral.Valid p q eta) :
    ∃ z k, compute p q eta = some (z,k) ∧
      |(z:ℝ)/1000000000000-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ 1/1000000 := by
  let M := matrixView (ExactSolve.preconditioner (moment p) (moment q) eta)
  let rho := selectedContraction p q M eta
  let bound := MatrixEstimator.initialBound p q eta
  let k := GeometricBudget.select rho bound MatrixEstimator.polynomialBudget
  let s := selectedScore (moment p) (moment q) M (mean p-mean q) eta k
  let steps := if MatrixPreconditioned.contraction (moment p) (moment q) M eta <
    baseContraction (moment p) (moment q) eta then 2*k else k
  refine ⟨roundScore s,steps,compute_eq p q eta h,?_⟩
  have hc := contraction_range p q M eta h.2.2
  have hb := GeometricBudget.select_budget rho bound MatrixEstimator.polynomialBudget hc.1 hc.2
    (by norm_num [MatrixEstimator.polynomialBudget])
  have hbR : (rho:ℝ)^k * (normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) ≤
      1/1000000-1/1000000000000 := by
    have hh : ((rho^k*bound:ℚ):ℝ) ≤ (MatrixEstimator.polynomialBudget:ℝ) := by exact_mod_cast hb
    simpa only [bound,MatrixEstimator.initialBound,MatrixEstimator.polynomialBudget,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
      Rat.cast_sub,Rat.cast_one,Rat.cast_ofNat,mul_div_assoc] using hh
  have he := selectedScore_error p q M eta h.2.2 (ExactSolve.preconditioner_correct p q eta h.2.2) k
  have hr := roundScore_error s
  have ht := abs_sub_le ((roundScore s:ℝ)/1000000000000)
    (s:ℝ) (Certificate.target (realRows p) (realRows q) (eta:ℝ))
  change |(s:ℝ)-_| ≤ (rho:ℝ)^k*(normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) at he
  linarith

theorem compute_valid (p q : List (Fin m → ℚ)) (eta : ℚ) (z : Int) (k : Nat)
    (h : compute p q eta = some (z,k)) : MatrixGeneral.Valid p q eta := by
  unfold compute at h
  split at h
  · cases h
  · rename_i hg
    simpa only [Bool.or_eq_true,List.isEmpty_iff,decide_eq_true_eq,not_or,not_le,
      and_assoc,MatrixGeneral.Valid] using hg

theorem compute_returned_error (p q : List (Fin m → ℚ)) (eta : ℚ) (z : Int) (k : Nat)
    (h : compute p q eta = some (z,k)) :
    |(z:ℝ)/1000000000000-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ 1/1000000 := by
  obtain ⟨z',k',hc,he⟩ := compute_correct p q eta (compute_valid p q eta z k h)
  have hz := Prod.mk.inj (Option.some.inj (hc.symm.trans h))
  obtain ⟨rfl,rfl⟩ := hz
  exact he

#print axioms compute_correct
#print axioms compute_returned_error
end Project.SpectralKL.MatrixAccelerated
