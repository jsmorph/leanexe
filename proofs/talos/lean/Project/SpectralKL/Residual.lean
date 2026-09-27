import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Residual certificates for the actual matrix functional. A candidate solve
may come from any implementation. The bound uses its computed residual and
the ridge parameter, rather than assuming that the solver is accurate. -/
namespace Project.SpectralKL.Residual
open Matrix Finset
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def Symmetric (M : Matrix n n ℝ) : Prop := ∀ i j, M i j = M j i

def Coercive (M : Matrix n n ℝ) (eta : ℝ) : Prop :=
  ∀ v, eta * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M *ᵥ v)

noncomputable def quadratic (M : Matrix n n ℝ) (d : n → ℝ) : ℝ :=
  d ⬝ᵥ (M⁻¹ *ᵥ d)

def energy (M : Matrix n n ℝ) (d x : n → ℝ) : ℝ :=
  2 * (d ⬝ᵥ x) - x ⬝ᵥ (M *ᵥ x)

theorem symmetric_pair (M : Matrix n n ℝ) (hM : Symmetric M) (x y : n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hM j i]
  ring

theorem self_nonneg (v : n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

theorem posDef (M : Matrix n n ℝ) (hM : Symmetric M)
    (eta : ℝ) (he : 0 < eta) (hc : Coercive M eta) : M.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simpa using hM j i
  · intro v hv
    have hp : 0 < v ⬝ᵥ v := lt_of_le_of_ne (self_nonneg v)
      (Ne.symm (fun h => hv (dotProduct_self_eq_zero.mp h)))
    simpa using (mul_pos he hp).trans_le (hc v)

theorem solve (M : Matrix n n ℝ) (hM : M.PosDef) (d : n → ℝ) :
    M *ᵥ (M⁻¹ *ᵥ d) = d := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit), Matrix.one_mulVec]

theorem energy_gap (M : Matrix n n ℝ) (hM : Symmetric M)
    (d x y : n → ℝ) (hy : M *ᵥ y = d) :
    d ⬝ᵥ y - energy M d x = (y-x) ⬝ᵥ (M *ᵥ (y-x)) := by
  have hp := symmetric_pair M hM x y
  rw [hy] at hp
  simp only [energy, Matrix.mulVec_sub, hy, sub_dotProduct, dotProduct_sub]
  rw [dotProduct_comm y d, ← hp, dotProduct_comm x d]
  ring

theorem residual_upper (M : Matrix n n ℝ) (eta : ℝ) (he : 0 < eta)
    (hc : Coercive M eta) (e : n → ℝ) :
    e ⬝ᵥ (M *ᵥ e) ≤ ((M *ᵥ e) ⬝ᵥ (M *ᵥ e)) / eta := by
  have hs : 0 ≤ ∑ i, (eta * e i - (M *ᵥ e) i)^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hid : (∑ i, (eta * e i - (M *ᵥ e) i)^2) =
      eta^2 * (e ⬝ᵥ e) - 2*eta*(e ⬝ᵥ (M *ᵥ e)) +
        ((M *ᵥ e) ⬝ᵥ (M *ᵥ e)) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid] at hs
  apply (le_div_iff₀ he).mpr
  nlinarith [mul_le_mul_of_nonneg_left (hc e) he.le]

/-- A lower and upper bound for the inverse quadratic form, valid for every
candidate vector x. No assumption about how x was computed occurs here. -/
theorem quadratic_bounds (M : Matrix n n ℝ) (hM : Symmetric M)
    (eta : ℝ) (he : 0 < eta) (hc : Coercive M eta) (d x : n → ℝ) :
    energy M d x ≤ quadratic M d ∧
      quadratic M d ≤ energy M d x + ((d-M*ᵥx) ⬝ᵥ (d-M*ᵥx))/eta := by
  let y := M⁻¹ *ᵥ d
  have hy : M *ᵥ y = d := solve M (posDef M hM eta he hc) d
  have hg := energy_gap M hM d x y hy
  have hr : M *ᵥ (y-x) = d-M*ᵥx := by rw [Matrix.mulVec_sub, hy]
  have hu := residual_upper M eta he hc (y-x)
  have hl := (mul_nonneg he.le (self_nonneg (y-x))).trans (hc (y-x))
  change energy M d x ≤ d ⬝ᵥ y ∧ d ⬝ᵥ y ≤ _
  rw [hr] at hu hg hl
  constructor <;> linarith

#print axioms quadratic_bounds
end Project.SpectralKL.Residual
