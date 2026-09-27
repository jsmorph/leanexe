import Project.SpectralKL.MatrixEstimator

namespace Project.SpectralKL.MatrixEstimator
open MatrixPolynomial Samples
variable {m : Nat}

def polynomialBudget : ℚ := 1/1000000-1/1000000000000

/-- Select a depth within the limit using the input-derived error bound.
No approximate output is used to choose this depth. -/
def depth (rho bound : ℚ) : Nat → Nat
  | 0 => 0
  | k+1 => if rho^k*bound ≤ polynomialBudget then depth rho bound k else k+1

theorem depth_le (rho bound : ℚ) (k : Nat) : depth rho bound k ≤ k := by
  induction k with
  | zero => simp [depth]
  | succ k ih => unfold depth; split <;> omega

theorem depth_budget (rho bound : ℚ) (k : Nat)
    (h : rho^k*bound ≤ polynomialBudget) :
    rho^(depth rho bound k)*bound ≤ polynomialBudget := by
  induction k with
  | zero => exact h
  | succ k ih =>
    unfold depth
    split
    · rename_i hs; exact ih hs
    · exact h

def contraction (p q : List (Fin m → ℚ)) (eta : ℚ) : ℚ :=
  (frobSqQ (moment p)+frobSqQ (moment q))/eta^2
def initialBound (p q : List (Fin m → ℚ)) (eta : ℚ) : ℚ :=
  normSqQ (mean p-mean q)/(2*eta)

theorem input_budget (p q : List (Fin m → ℚ)) (eta : ℚ) (h : Valid p q eta) :
    0 ≤ contraction p q eta ∧
    (contraction p q eta)^12 * initialBound p q eta ≤ polynomialBudget := by
  have hf : 0 ≤ frobSqQ (moment p)+frobSqQ (moment q) := by
    unfold frobSqQ
    positivity
  have hd : 0 ≤ normSqQ (mean p-mean q) := by unfold normSqQ; positivity
  have ep : 0 < eta^2 := sq_pos_of_pos h.2.2.1
  have hc0 : 0 ≤ contraction p q eta := div_nonneg hf ep.le
  have hc : contraction p q eta ≤ 1/4 := by
    apply (div_le_iff₀ ep).mpr
    linarith [h.2.2.2.1]
  have hb0 : 0 ≤ initialBound p q eta := div_nonneg hd (by linarith [h.2.2.1])
  have hb : initialBound p q eta ≤ 16 := by
    apply (div_le_iff₀ (by linarith [h.2.2.1] : 0 < 2*eta)).mpr
    linarith [h.2.2.2.2]
  have hp := pow_le_pow_left₀ hc0 hc 12
  have ht := mul_le_mul hp hb hb0 (by norm_num : (0:ℚ) ≤ (1/4)^12)
  exact ⟨hc0,ht.trans (by norm_num [polynomialBudget])⟩

/-- The improved estimator selects a depth from its computed input moments.
The result contains the decimal score and the number of iteration steps. -/
def computeAdaptive (p q : List (Fin m → ℚ)) (eta : ℚ) : Option (Int × Nat) :=
  if p.isEmpty || q.isEmpty || eta ≤ 0 then none
  else
    let a := storedMoment p
    let b := storedMoment q
    let d := MatrixPolynomial.store (MatrixPolynomial.view (storedMean p)-MatrixPolynomial.view (storedMean q))
    let f := frobSqQ (matrixView a)+frobSqQ (matrixView b)
    let d2 := normSqQ (MatrixPolynomial.view d)
    if f > eta^2/4 || d2 > 32*eta then none
    else
      let k := depth (f/eta^2) (d2/(2*eta)) 12
      some (roundScore (score (matrixView a) (matrixView b) (MatrixPolynomial.view d) eta k),k)

theorem computeAdaptive_eq (p q : List (Fin m → ℚ)) (eta : ℚ) (h : Valid p q eta) :
    computeAdaptive p q eta =
      let k := depth (contraction p q eta) (initialBound p q eta) 12
      some (roundScore (sampleScore p q eta k),k) := by
  simp [computeAdaptive,h.1,h.2.1,not_le.mpr h.2.2.1,not_lt.mpr h.2.2.2.1,
    not_lt.mpr h.2.2.2.2,contraction,initialBound,sampleScore]

theorem computeAdaptive_correct (p q : List (Fin m → ℚ)) (eta : ℚ) (h : Valid p q eta) :
    ∃ z k, computeAdaptive p q eta = some (z,k) ∧ k ≤ 12 ∧
      |(z:ℝ)/1000000000000-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ 1/1000000 := by
  let rho := contraction p q eta
  let bound := initialBound p q eta
  let k := depth rho bound 12
  refine ⟨roundScore (sampleScore p q eta k),k,computeAdaptive_eq p q eta h,depth_le rho bound 12,?_⟩
  have hi := input_budget p q eta h
  have hm : frobSqQ (moment p)+frobSqQ (moment q) ≤ rho*eta^2 := by
    dsimp [rho,contraction]
    rw [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos h.2.2.1))]
  have he := sampleScore_error_with p q eta h.2.2.1 rho hi.1 hm k
  have hb := depth_budget rho bound 12 hi.2
  have hbR : (rho:ℝ)^k * (normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) ≤
      1/1000000-1/1000000000000 := by
    have hh : ((rho^k*bound:ℚ):ℝ) ≤ (polynomialBudget:ℝ) := by exact_mod_cast hb
    simpa only [bound,initialBound,polynomialBudget,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
      Rat.cast_sub,Rat.cast_one,Rat.cast_ofNat,mul_div_assoc] using hh
  have hr := roundScore_error (sampleScore p q eta k)
  have ht := abs_sub_le ((roundScore (sampleScore p q eta k):ℝ)/1000000000000)
    (sampleScore p q eta k:ℝ) (Certificate.target (realRows p) (realRows q) (eta:ℝ))
  linarith

theorem computeAdaptive_valid (p q : List (Fin m → ℚ)) (eta : ℚ) (z : Int) (k : Nat)
    (h : computeAdaptive p q eta = some (z,k)) : Valid p q eta := by
  unfold computeAdaptive at h
  split at h
  · cases h
  · rename_i hg
    simp only [Bool.or_eq_true, List.isEmpty_iff, decide_eq_true_eq, not_or, not_le] at hg
    dsimp only at h
    simp only [storedMoment_eq,MatrixPolynomial.view_store,storedMean_eq] at h
    split at h
    · cases h
    · rename_i hs
      simp only [Bool.or_eq_true,decide_eq_true_eq,not_or,not_lt] at hs
      exact ⟨hg.1.1,hg.1.2,hg.2,hs.1,hs.2⟩

theorem computeAdaptive_returned_error (p q : List (Fin m → ℚ)) (eta : ℚ) (z : Int) (k : Nat)
    (h : computeAdaptive p q eta = some (z,k)) :
    |(z:ℝ)/1000000000000-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ 1/1000000 := by
  obtain ⟨z',k',hc,_,he⟩ := computeAdaptive_correct p q eta (computeAdaptive_valid p q eta z k h)
  have hz := Prod.mk.inj (Option.some.inj (hc.symm.trans h))
  obtain ⟨rfl,rfl⟩ := hz
  exact he

#print axioms computeAdaptive_correct
#print axioms computeAdaptive_returned_error
end Project.SpectralKL.MatrixEstimator
