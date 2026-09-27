import Project.Beck.MinorState

namespace Project.Beck.MinorKernel

open Matrix MinorState

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {width : ℕ}

theorem row_sum (blocks : Blocks ι) (row : ℕ) (vector : Fin width → ℚ)
    (nonzero : blocks.leading.det ≠ 0)
    (topZero : ∀ i, ∑ col, (blocks.top i col.val : ℚ) * vector col = 0) :
    ∑ col, (minor blocks row col.val : ℚ) * vector col =
      (blocks.leading.det : ℚ) * ∑ col, (blocks.rest row col.val : ℚ) * vector col := by
  let A : Matrix ι ι ℚ := blocks.leading.map Int.cast
  have detNonzero : A.det ≠ 0 := by
    dsimp [A]
    rw [← Int.cast_det]
    exact_mod_cast nonzero
  let : Invertible A.det := invertibleOfNonzero detNonzero
  let : Invertible A := invertibleOfDetInvertible A
  have entry (col : Fin width) :
      (minor blocks row col.val : ℚ) = A.det *
        ((blocks.rest row col.val : ℚ) -
          ∑ j, (∑ i, (blocks.left row i : ℚ) * (⅟A) i j) * (blocks.top j col.val : ℚ)) := by
    unfold minor bordered
    erw [Int.cast_det, fromBlocks_map, Matrix.det_fromBlocks₁₁, det_fin_one]
    rfl
  simp_rw [entry, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have correction : (∑ col : Fin width,
      (A.det * ∑ j, (∑ i, (blocks.left row i : ℚ) * (⅟A) i j) *
        (blocks.top j col.val : ℚ)) * vector col) = 0 := by
    calc
      _ = A.det * ∑ col : Fin width, ∑ j,
          (∑ i, (blocks.left row i : ℚ) * (⅟A) i j) *
            ((blocks.top j col.val : ℚ) * vector col) := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = A.det * ∑ j, (∑ i, (blocks.left row i : ℚ) * (⅟A) i j) *
          ∑ col : Fin width, (blocks.top j col.val : ℚ) * vector col := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = 0 := by simp only [topZero, mul_zero, Finset.sum_const_zero]
  rw [correction, sub_zero]
  simp only [mul_assoc, ← Finset.mul_sum, A, ← Int.cast_det]

def direction (blocks : Blocks ι) (columns : ι → Fin width) (free : Fin width) :
    Fin width → ℤ := fun col =>
  (if col = free then blocks.leading.det else 0) -
    ∑ i, if col = columns i then blocks.leading.cramer (fun j => blocks.top j free.val) i else 0

theorem free_value (blocks : Blocks ι) (columns : ι → Fin width) (free : Fin width)
    (distinct : ∀ i, columns i ≠ free) :
    direction blocks columns free free = blocks.leading.det := by
  simp [direction, fun i => Ne.symm (distinct i)]

theorem selected_value (blocks : Blocks ι) (columns : ι → Fin width) (free : Fin width)
    (injective : Function.Injective columns) (distinct : ∀ i, columns i ≠ free) (i : ι) :
    direction blocks columns free (columns i) =
      -blocks.leading.cramer (fun j => blocks.top j free.val) i := by
  simp [direction, distinct, injective.eq_iff]

theorem other_value (blocks : Blocks ι) (columns : ι → Fin width) (free col : Fin width)
    (notFree : col ≠ free) (notSelected : ∀ i, col ≠ columns i) :
    direction blocks columns free col = 0 := by
  simp [direction, notFree, notSelected]

theorem selected_rows (blocks : Blocks ι) (columns : ι → Fin width) (free : Fin width)
    (leading : ∀ i j, blocks.leading i j = blocks.top i (columns j).val) (row : ι) :
    ∑ col, blocks.top row col.val * direction blocks columns free col = 0 := by
  simp only [direction, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun col i => blocks.top row col.val *
    (if col = columns i then blocks.leading.cramer (fun j => blocks.top j free.val) i else 0))]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have cramer := congrFun (blocks.leading.mulVec_cramer (fun j => blocks.top j free.val)) row
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, leading] at cramer
  rw [cramer]
  ring

#print axioms row_sum
#print axioms selected_rows

end Project.Beck.MinorKernel
