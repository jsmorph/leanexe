import Project.SpectralKL.MatrixGeneral

namespace Project.SpectralKL.MatrixGeneral
open MatrixPolynomial MatrixEstimator Samples
variable {m : Nat}

def selectedContraction (p q : List (Fin m → ℚ)) (eta : ℚ) : ℚ :=
  min (MatrixEstimator.contraction p q eta) (MatrixDamped.contraction p q eta)

def selectedScore (A B : Matrix (Fin m) (Fin m) ℚ) (d : Fin m → ℚ) (eta : ℚ)
    (k : Nat) : ℚ :=
  if (frobSqQ A+frobSqQ B)/eta^2 ≤ 1-eta^2/MatrixDamped.upperSqQ A B eta then
    MatrixPolynomial.score A B d eta k
  else MatrixDamped.score A B d eta k

def selectedSampleScore (p q : List (Fin m → ℚ)) (eta : ℚ) (k : Nat) : ℚ :=
  selectedScore (moment p) (moment q) (mean p-mean q) eta k

theorem selectedContraction_range (p q : List (Fin m → ℚ)) (eta : ℚ) (he : 0 < eta) :
    0 ≤ selectedContraction p q eta ∧ selectedContraction p q eta < 1 := by
  have hd := contraction_range p q eta he
  have hf : 0 ≤ MatrixEstimator.contraction p q eta := by
    unfold MatrixEstimator.contraction frobSqQ
    positivity
  exact ⟨le_min hf hd.1,(min_le_right _ _).trans_lt hd.2⟩

theorem selectedSampleScore_error (p q : List (Fin m → ℚ)) (eta : ℚ)
    (he : 0 < eta) (k : Nat) :
    |(selectedSampleScore p q eta k:ℝ)-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤
      (selectedContraction p q eta:ℝ)^k * (normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) := by
  have hscore : selectedSampleScore p q eta k =
      if MatrixEstimator.contraction p q eta ≤ MatrixDamped.contraction p q eta then
        MatrixPolynomial.sampleScore p q eta k else MatrixDamped.sampleScore p q eta k := rfl
  rw [hscore]
  by_cases hf : MatrixEstimator.contraction p q eta ≤ MatrixDamped.contraction p q eta
  · have hr : 0 ≤ MatrixEstimator.contraction p q eta := by
      unfold MatrixEstimator.contraction frobSqQ
      positivity
    have hm : frobSqQ (moment p)+frobSqQ (moment q) ≤
        MatrixEstimator.contraction p q eta*eta^2 := by
      rw [MatrixEstimator.contraction,div_mul_cancel₀ _ (sq_pos_of_pos he).ne']
    have hs := MatrixPolynomial.sampleScore_error_with p q eta he _ hr hm k
    simpa only [selectedContraction,min_eq_left hf,if_pos hf] using hs
  · have hs := MatrixDamped.sampleScore_error p q eta he k
    simpa only [selectedContraction,min_eq_right (le_of_not_ge hf),if_neg hf] using hs

/-- Compute moments once, select the smaller proved contraction factor, and run
the corresponding polynomial algorithm for a sufficient number of steps. -/
def computeMoments (a b : StoredMatrix m) (d : Vector ℚ m) (eta : ℚ) : Int × Nat :=
  let f := frobSqQ (matrixView a)+frobSqQ (matrixView b)
  let u := MatrixDamped.upperSqQ (matrixView a) (matrixView b) eta
  let rho := min (f/eta^2) (1-eta^2/u)
  let bound := normSqQ (view d)/(2*eta)
  let k := GeometricBudget.select rho bound polynomialBudget
  (roundScore (selectedScore (matrixView a) (matrixView b) (view d) eta k),k)

def computeAuto (p q : List (Fin m → ℚ)) (eta : ℚ) : Option (Int × Nat) :=
  if p.isEmpty || q.isEmpty || eta ≤ 0 then none
  else
    let a := storedMoment p
    let b := storedMoment q
    let d := store (view (storedMean p)-view (storedMean q))
    some (computeMoments a b d eta)

theorem computeAuto_eq (p q : List (Fin m → ℚ)) (eta : ℚ) (h : Valid p q eta) :
    computeAuto p q eta =
      let k := GeometricBudget.select (selectedContraction p q eta)
        (initialBound p q eta) polynomialBudget
      some (roundScore (selectedSampleScore p q eta k),k) := by
  simp [computeAuto,computeMoments,h.1,h.2.1,not_le.mpr h.2.2,selectedContraction,MatrixDamped.contraction,
    MatrixEstimator.contraction,initialBound,selectedSampleScore]

theorem computeAuto_correct (p q : List (Fin m → ℚ)) (eta : ℚ) (h : Valid p q eta) :
    ∃ z k, computeAuto p q eta = some (z,k) ∧
      |(z:ℝ)/1000000000000-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ 1/1000000 := by
  let rho := selectedContraction p q eta
  let bound := initialBound p q eta
  let k := GeometricBudget.select rho bound polynomialBudget
  refine ⟨roundScore (selectedSampleScore p q eta k),k,computeAuto_eq p q eta h,?_⟩
  have hc := selectedContraction_range p q eta h.2.2
  have hb := GeometricBudget.select_budget rho bound polynomialBudget hc.1 hc.2
    (by norm_num [polynomialBudget])
  have hbR : (rho:ℝ)^k * (normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) ≤
      1/1000000-1/1000000000000 := by
    have hh : ((rho^k*bound:ℚ):ℝ) ≤ (polynomialBudget:ℝ) := by exact_mod_cast hb
    simpa only [bound,initialBound,polynomialBudget,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
      Rat.cast_sub,Rat.cast_one,Rat.cast_ofNat,mul_div_assoc] using hh
  have he := selectedSampleScore_error p q eta h.2.2 k
  have hr := roundScore_error (selectedSampleScore p q eta k)
  have ht := abs_sub_le ((roundScore (selectedSampleScore p q eta k):ℝ)/1000000000000)
    (selectedSampleScore p q eta k:ℝ) (Certificate.target (realRows p) (realRows q) (eta:ℝ))
  change |(selectedSampleScore p q eta k:ℝ)-_| ≤
    (rho:ℝ)^k*(normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) at he
  linarith

theorem computeAuto_valid (p q : List (Fin m → ℚ)) (eta : ℚ) (z : Int) (k : Nat)
    (h : computeAuto p q eta = some (z,k)) : Valid p q eta := by
  unfold computeAuto at h
  split at h
  · cases h
  · rename_i hg
    simpa only [Bool.or_eq_true,List.isEmpty_iff,decide_eq_true_eq,not_or,not_le,
      and_assoc,Valid] using hg

theorem computeAuto_returned_error (p q : List (Fin m → ℚ)) (eta : ℚ) (z : Int) (k : Nat)
    (h : computeAuto p q eta = some (z,k)) :
    |(z:ℝ)/1000000000000-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ 1/1000000 := by
  obtain ⟨z',k',hc,he⟩ := computeAuto_correct p q eta (computeAuto_valid p q eta z k h)
  have hz := Prod.mk.inj (Option.some.inj (hc.symm.trans h))
  obtain ⟨rfl,rfl⟩ := hz
  exact he

#print axioms computeAuto_correct
#print axioms computeAuto_returned_error
end Project.SpectralKL.MatrixGeneral
