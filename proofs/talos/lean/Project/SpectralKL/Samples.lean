import Project.SpectralKL.Residual
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Star.Real

namespace Project.SpectralKL.Samples
open Matrix
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def meanSum {K : Type*} [Field K] : List (n → K) → n → K
  | [] => 0
  | v :: vs => v + meanSum vs

def mean {K : Type*} [Field K] (rows : List (n → K)) : n → K :=
  (1 / (rows.length : K)) • meanSum rows

/-- Applying the moment matrix directly to a candidate costs one projection
and one vector update per observation. The checker does not recompute a Gram
matrix or repeat the eigensolver. -/
def actionSum {K : Type*} [Field K] (x : n → K) : List (n → K) → n → K
  | [] => 0
  | v :: vs => (v ⬝ᵥ x) • v + actionSum x vs

def action {K : Type*} [Field K] (rows : List (n → K)) (x : n → K) : n → K :=
  (1 / (rows.length : K)) • actionSum x rows

def gramSum {K : Type*} [Field K] : List (n → K) → Matrix n n K
  | [] => 0
  | v :: vs => vecMulVec v v + gramSum vs

def moment {K : Type*} [Field K] (rows : List (n → K)) : Matrix n n K :=
  (1 / (rows.length : K)) • gramSum rows

theorem gramSum_action {K : Type*} [Field K] (rows : List (n → K)) (x : n → K) :
    gramSum rows *ᵥ x = actionSum x rows := by
  induction rows with
  | nil => simp [gramSum, actionSum]
  | cons v vs ih =>
    simp [gramSum, actionSum, Matrix.add_mulVec, ih, Matrix.vecMulVec_mulVec]

theorem moment_action {K : Type*} [Field K] (rows : List (n → K)) (x : n → K) :
    moment rows *ᵥ x = action rows x := by
  simp [moment, action, Matrix.smul_mulVec, gramSum_action]

theorem gramSum_psd (rows : List (n → ℝ)) : (gramSum rows).PosSemidef := by
  induction rows with
  | nil => exact Matrix.PosSemidef.zero
  | cons v vs ih =>
    have hv : (vecMulVec v v).PosSemidef := by
      simpa using Matrix.posSemidef_vecMulVec_self_star v
    exact hv.add ih

theorem moment_psd (rows : List (n → ℝ)) : (moment rows).PosSemidef :=
  (gramSum_psd rows).smul (by positivity)

def system {K : Type*} [Field K] (p q : List (n → K)) (eta r : K) : Matrix n n K :=
  r • moment p + (1-r) • moment q + eta • 1

def systemAction {K : Type*} [Field K] (p q : List (n → K)) (eta r : K)
    (x : n → K) : n → K :=
  r • action p x + (1-r) • action q x + eta • x

theorem system_action {K : Type*} [Field K] (p q : List (n → K)) (eta r : K)
    (x : n → K) : system p q eta r *ᵥ x = systemAction p q eta r x := by
  simp [system, systemAction, Matrix.add_mulVec, Matrix.smul_mulVec,
    moment_action, Matrix.one_mulVec]

theorem system_symmetric (p q : List (n → ℝ)) (eta r : ℝ) :
    Residual.Symmetric (system p q eta r) := by
  have hs : (system p q eta r).IsHermitian := by
    unfold system
    exact (((moment_psd p).isHermitian.smul (show star r = r by rfl)).add
      ((moment_psd q).isHermitian.smul (show star (1-r) = 1-r by rfl))).add
      (Matrix.isHermitian_one.smul (show star eta = eta by rfl))
  intro i j
  have h := congrFun (congrFun hs i) j
  simpa using h.symm

theorem system_coercive (p q : List (n → ℝ)) (eta r : ℝ)
    (hr : r ∈ Set.Icc (0:ℝ) 1) : Residual.Coercive (system p q eta r) eta := by
  intro v
  have h := (((moment_psd p).smul hr.1).add
    ((moment_psd q).smul (sub_nonneg.mpr hr.2))).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at h
  simp only [system, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul] at h
  linarith

def realRows (rows : List (n → ℚ)) : List (n → ℝ) := rows.map fun v i => (v i : ℝ)
def realVec (v : n → ℚ) : n → ℝ := fun i => (v i : ℝ)

theorem dot_cast (x y : n → ℚ) : ((x ⬝ᵥ y : ℚ) : ℝ) = realVec x ⬝ᵥ realVec y := by
  simp [dotProduct, realVec]

theorem meanSum_cast (rows : List (n → ℚ)) :
    realVec (meanSum rows) = meanSum (realRows rows) := by
  induction rows with
  | nil => ext i; simp [meanSum, realRows, realVec]
  | cons v vs ih =>
    ext i
    have hi := congrFun ih i
    simpa [meanSum, realRows, realVec] using congrArg (fun t => (v i : ℝ) + t) hi

theorem mean_cast (rows : List (n → ℚ)) :
    realVec (mean rows) = mean (realRows rows) := by
  ext i
  have hi := congrFun (meanSum_cast rows) i
  simpa only [mean, realVec, Pi.smul_apply, smul_eq_mul, Rat.cast_mul,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast, realRows, List.length_map] using
      congrArg (fun t => (1 / (rows.length : ℝ)) * t) hi

theorem actionSum_cast (rows : List (n → ℚ)) (x : n → ℚ) :
    realVec (actionSum x rows) = actionSum (realVec x) (realRows rows) := by
  induction rows with
  | nil => ext i; simp [actionSum, realRows, realVec]
  | cons v vs ih =>
    ext i
    have hi := congrFun ih i
    convert congrArg (fun t => (realVec v ⬝ᵥ realVec x) * (v i : ℝ) + t) hi using 1 <;>
      simp only [actionSum, realRows, List.map_cons, realVec, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Rat.cast_add, Rat.cast_mul, dot_cast] <;> rfl

theorem action_cast (rows : List (n → ℚ)) (x : n → ℚ) :
    realVec (action rows x) = action (realRows rows) (realVec x) := by
  ext i
  have hi := congrFun (actionSum_cast rows x) i
  simpa only [action, realVec, Pi.smul_apply, smul_eq_mul, Rat.cast_mul,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast, realRows, List.length_map] using
      congrArg (fun t => (1 / (rows.length : ℝ)) * t) hi

#print axioms system_coercive
#print axioms action_cast
end Project.SpectralKL.Samples
