import Project.Beck.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace Project.Beck.Cofactors

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def border (A : Matrix ι ι ℚ) (b c : ι → ℚ) (a : ℚ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℚ :=
  Matrix.fromBlocks A (Matrix.of fun i _ => b i)
    (Matrix.of fun _ j => c j) (Matrix.of fun _ _ => a)

def direction (A : Matrix ι ι ℚ) (b : ι → ℚ) : ι ⊕ Unit → ℚ :=
  Sum.elim (fun j => -A.cramer b j) (fun _ => A.det)

theorem border_det (A : Matrix ι ι ℚ) (b c : ι → ℚ) (a : ℚ)
    (nonzero : A.det ≠ 0) :
    (border A b c a).det = a * A.det - dotProduct c (A.cramer b) := by
  let : Invertible A := A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr nonzero)
  have cramer := A.det_smul_inv_mulVec_eq_cramer b (isUnit_iff_ne_zero.mpr nonzero)
  erw [border, Matrix.det_fromBlocks₁₁, Matrix.det_unique (n := Unit),
    Matrix.invOf_eq_nonsing_inv]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [← cramer]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem direction_nonzero (A : Matrix ι ι ℚ) (b : ι → ℚ) (h : A.det ≠ 0) :
    direction A b ≠ 0 := by
  intro zero
  have := congrFun zero (Sum.inr ())
  exact h this

theorem selected_row_preserved (A : Matrix ι ι ℚ) (b : ι → ℚ) (i : ι) :
    (∑ j, A i j * (-A.cramer b j)) + b i * A.det = 0 := by
  have h := congrFun (A.mulVec_cramer b) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  simp only [mul_neg, Finset.sum_neg_distrib]
  rw [h]
  ring

theorem other_row_preserved (A : Matrix ι ι ℚ) (b c : ι → ℚ) (a : ℚ)
    (nonzero : A.det ≠ 0) (maximal : (border A b c a).det = 0) :
    (∑ j, c j * (-A.cramer b j)) + a * A.det = 0 := by
  rw [border_det A b c a nonzero] at maximal
  simp only [mul_neg, Finset.sum_neg_distrib, dotProduct] at *
  linarith

end Project.Beck.Cofactors
