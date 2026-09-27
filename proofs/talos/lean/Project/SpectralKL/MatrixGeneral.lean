import Project.SpectralKL.MatrixDampedPolynomial
import Project.SpectralKL.GeometricBudget

namespace Project.SpectralKL.MatrixGeneral
open MatrixPolynomial MatrixEstimator Samples
variable {m : Nat}

def Valid (p q : List (Fin m → ℚ)) (eta : ℚ) : Prop :=
  p ≠ [] ∧ q ≠ [] ∧ 0 < eta

/-- Full sample computation for every positive ridge. The finite search budget is
derived from the input moments, independently of any proposed output. -/
def compute (p q : List (Fin m → ℚ)) (eta : ℚ) : Option (Int × Nat) :=
  if p.isEmpty || q.isEmpty || eta ≤ 0 then none
  else
    let a := storedMoment p
    let b := storedMoment q
    let d := store (view (storedMean p)-view (storedMean q))
    let u := MatrixDamped.upperSqQ (matrixView a) (matrixView b) eta
    let rho := 1-eta^2/u
    let bound := normSqQ (view d)/(2*eta)
    let k := GeometricBudget.select rho bound polynomialBudget
    some (roundScore (MatrixDamped.score (matrixView a) (matrixView b) (view d) eta k),k)

theorem contraction_range (p q : List (Fin m → ℚ)) (eta : ℚ) (he : 0 < eta) :
    0 ≤ MatrixDamped.contraction p q eta ∧ MatrixDamped.contraction p q eta < 1 := by
  have hp : 0 ≤ frobSqQ (moment p) := by unfold frobSqQ; positivity
  have hq : 0 ≤ frobSqQ (moment q) := by unfold frobSqQ; positivity
  have hs := sq_pos_of_pos he
  have hu : 0 < MatrixDamped.upperSqQ (moment p) (moment q) eta := by
    unfold MatrixDamped.upperSqQ
    positivity
  unfold MatrixDamped.contraction
  constructor
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ hu).mpr
    unfold MatrixDamped.upperSqQ
    nlinarith
  · linarith [div_pos hs hu]

theorem compute_eq (p q : List (Fin m → ℚ)) (eta : ℚ) (h : Valid p q eta) :
    compute p q eta =
      let k := GeometricBudget.select (MatrixDamped.contraction p q eta)
        (initialBound p q eta) polynomialBudget
      some (roundScore (MatrixDamped.sampleScore p q eta k),k) := by
  simp [compute,h.1,h.2.1,not_le.mpr h.2.2,MatrixDamped.contraction,
    initialBound,MatrixDamped.sampleScore]

/-- Total correctness of the executed sample estimator, without a condition relating
the ridge to the moments or bounding the mean difference. -/
theorem compute_correct (p q : List (Fin m → ℚ)) (eta : ℚ) (h : Valid p q eta) :
    ∃ z k, compute p q eta = some (z,k) ∧
      |(z:ℝ)/1000000000000-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ 1/1000000 := by
  let rho := MatrixDamped.contraction p q eta
  let bound := initialBound p q eta
  let k := GeometricBudget.select rho bound polynomialBudget
  refine ⟨roundScore (MatrixDamped.sampleScore p q eta k),k,compute_eq p q eta h,?_⟩
  have hc := contraction_range p q eta h.2.2
  have hb := GeometricBudget.select_budget rho bound polynomialBudget hc.1 hc.2
    (by norm_num [polynomialBudget])
  have hbR : (rho:ℝ)^k * (normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) ≤
      1/1000000-1/1000000000000 := by
    have hh : ((rho^k*bound:ℚ):ℝ) ≤ (polynomialBudget:ℝ) := by exact_mod_cast hb
    simpa only [bound,initialBound,polynomialBudget,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
      Rat.cast_sub,Rat.cast_one,Rat.cast_ofNat,mul_div_assoc] using hh
  have he := MatrixDamped.sampleScore_error p q eta h.2.2 k
  have hr := roundScore_error (MatrixDamped.sampleScore p q eta k)
  have ht := abs_sub_le ((roundScore (MatrixDamped.sampleScore p q eta k):ℝ)/1000000000000)
    (MatrixDamped.sampleScore p q eta k:ℝ) (Certificate.target (realRows p) (realRows q) (eta:ℝ))
  change |(MatrixDamped.sampleScore p q eta k:ℝ)-_| ≤
    (rho:ℝ)^k*(normSqQ (mean p-mean q):ℝ)/(2*(eta:ℝ)) at he
  linarith

theorem compute_valid (p q : List (Fin m → ℚ)) (eta : ℚ) (z : Int) (k : Nat)
    (h : compute p q eta = some (z,k)) : Valid p q eta := by
  unfold compute at h
  split at h
  · cases h
  · rename_i hg
    simpa only [Bool.or_eq_true,List.isEmpty_iff,decide_eq_true_eq,not_or,not_le,
      and_assoc,Valid] using hg

theorem compute_returned_error (p q : List (Fin m → ℚ)) (eta : ℚ) (z : Int) (k : Nat)
    (h : compute p q eta = some (z,k)) :
    |(z:ℝ)/1000000000000-Certificate.target (realRows p) (realRows q) (eta:ℝ)| ≤ 1/1000000 := by
  obtain ⟨z',k',hc,he⟩ := compute_correct p q eta (compute_valid p q eta z k h)
  have hz := Prod.mk.inj (Option.some.inj (hc.symm.trans h))
  obtain ⟨rfl,rfl⟩ := hz
  exact he

#print axioms compute_correct
#print axioms compute_returned_error
end Project.SpectralKL.MatrixGeneral
