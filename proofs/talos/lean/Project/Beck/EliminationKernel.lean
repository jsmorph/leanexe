import Project.Beck.EliminationModel

namespace Project.Beck.Elimination

open LeanExe.Examples.BeckExact IntegerAdd

def rationalRow (width : ℕ) (matrix : Array Integer) (row : ℕ) : Fin width → ℚ :=
  fun col => (value matrix[row * width + col.val]! : ℚ)

def rationalValues (width : ℕ) (matrix : Array ℤ) (row : ℕ) : Fin width → ℚ :=
  fun col => (matrix[row * width + col.val]! : ℚ)

theorem model_row_eq (width rows rank column row : ℕ) (matrix : Array Integer) (previous : Integer)
    (size : matrix.size = rows * width) (rankBound : rank < rows) (columnBound : column < width)
    (rowBound : row < rows) (nonzero : value previous ≠ 0)
    (prefixZero : ∀ r, rank ≤ r → r < rows → ∀ c, c < column →
      value matrix[r * width + c]! = 0)
    (divides : ∀ r, rank < r → r < rows → ∀ c, column < c → c < width →
      value previous ∣ value matrix[rank * width + column]! * value matrix[r * width + c]! -
        value matrix[r * width + column]! * value matrix[rank * width + c]!) :
    rationalValues width (model width rows rank column matrix previous) row =
      if rank < row then
        Bareiss.reduceRow (rationalRow width matrix rank) (rationalRow width matrix row)
          ⟨column, columnBound⟩ (value previous)
      else rationalRow width matrix row := by
  by_cases later : rank < row
  · rw [ite_eq_left later]
    funext col
    change ((model width rows rank column matrix previous)[row * width + col.val]! : ℚ) = _
    rw [model_get width rows rank column row col.val matrix previous size rankBound columnBound
      rowBound col.isLt, ite_eq_left later]
    dsimp only [Bareiss.reduceRow, rationalRow]
    by_cases afterColumn : column < col.val
    · rw [ite_eq_left afterColumn, entryValue, Int.cast_div
        (divides row later rowBound col.val afterColumn col.isLt) (by exact_mod_cast nonzero)]
      push_cast
      rfl
    · by_cases sameColumn : col.val = column
      · simp [sameColumn, mul_comm]
      · have earlier : col.val < column := by omega
        have rowZero := prefixZero row (by omega) rowBound col.val earlier
        have pivotZero := prefixZero rank (by rfl) rankBound col.val earlier
        simp [afterColumn, sameColumn, rowZero, pivotZero]
  · rw [ite_eq_right later]
    funext col
    change ((model width rows rank column matrix previous)[row * width + col.val]! : ℚ) = _
    rw [model_get width rows rank column row col.val matrix previous size rankBound columnBound
      rowBound col.isLt, ite_eq_right later]
    rfl

theorem model_kernel (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (size : matrix.size = rows * width) (rankBound : rank < rows) (columnBound : column < width)
    (nonzero : value previous ≠ 0) (pivotNonzero : value matrix[rank * width + column]! ≠ 0)
    (prefixZero : ∀ r, rank ≤ r → r < rows → ∀ c, c < column →
      value matrix[r * width + c]! = 0)
    (divides : ∀ r, rank < r → r < rows → ∀ c, column < c → c < width →
      value previous ∣ value matrix[rank * width + column]! * value matrix[r * width + c]! -
        value matrix[r * width + column]! * value matrix[rank * width + c]!)
    (vector : Fin width → ℚ) :
    (∀ row : Fin rows, ∑ col, rationalValues width (model width rows rank column matrix previous)
        row.val col * vector col = 0) ↔
      (∀ row : Fin rows, ∑ col, rationalRow width matrix row.val col * vector col = 0) := by
  have rowEquation (row : Fin rows) := model_row_eq width rows rank column row.val matrix previous
    size rankBound columnBound row.isLt nonzero prefixZero divides
  have pivotEquation : rationalValues width (model width rows rank column matrix previous) rank =
      rationalRow width matrix rank := by
    simpa using rowEquation ⟨rank, rankBound⟩
  constructor
  · intro reduced
    have pivotZero : ∑ col, rationalRow width matrix rank col * vector col = 0 := by
      rw [← pivotEquation]
      exact reduced ⟨rank, rankBound⟩
    intro row
    have result := reduced row
    rw [rowEquation row] at result
    split at result
    · exact (Bareiss.reduceRow_zero_iff _ _ vector ⟨column, columnBound⟩ (value previous)
        (by
          change (value matrix[rank * width + column]! : ℚ) ≠ 0
          exact_mod_cast pivotNonzero) (by exact_mod_cast nonzero) pivotZero).mp result
    · exact result
  · intro original row
    rw [rowEquation row]
    split
    · rw [Bareiss.reduceRow_sum, original row, original ⟨rank, rankBound⟩]
      simp
    · exact original row

#print axioms model_kernel

theorem represents_row (width row : ℕ) (source : Array Integer) (target : Array ℤ)
    (related : Represents source target)
    (inside : ∀ col : Fin width, row * width + col.val < source.size) :
    rationalRow width source row = rationalValues width target row := by
  funext col
  rw [← related.2]
  dsimp only [rationalRow, rationalValues]
  rw [getElem!_pos (source.map value) (row * width + col.val) (by simpa using inside col),
    Array.getElem_map, getElem!_pos source (row * width + col.val) (inside col)]

theorem eliminate_preserves (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (size : matrix.size = rows * width) (rankBound : rank < rows) (columnBound : column < width)
    (valid : ∀ entry ∈ matrix, Valid entry) (previousValid : Valid previous)
    (nonzero : value previous ≠ 0) (pivotNonzero : value matrix[rank * width + column]! ≠ 0)
    (prefixZero : ∀ r, rank ≤ r → r < rows → ∀ c, c < column →
      value matrix[r * width + c]! = 0)
    (divides : ∀ r, rank < r → r < rows → ∀ c, column < c → c < width →
      value previous ∣ value matrix[rank * width + column]! * value matrix[r * width + c]! -
        value matrix[r * width + column]! * value matrix[rank * width + c]!) :
    ∃ result, eliminate width rows rank column matrix previous = some result ∧
      (∀ entry ∈ result, Valid entry) ∧ result.size = matrix.size ∧
      ∀ vector : Fin width → ℚ,
        (∀ row : Fin rows, ∑ col, rationalRow width result row.val col * vector col = 0) ↔
          (∀ row : Fin rows, ∑ col, rationalRow width matrix row.val col * vector col = 0) := by
  obtain ⟨result, source, related⟩ := eliminate_correct width rows rank column matrix previous
    size rankBound columnBound valid previousValid nonzero divides
  have resultSize : result.size = matrix.size := by
    have sizes := congrArg Array.size related.2
    simpa only [Array.size_map, model_size] using sizes
  have rowRelated (row : Fin rows) := represents_row width row.val result _ related (by
    intro col
    rw [resultSize, size]
    have rowBound := row.isLt
    have colBound := col.isLt
    nlinarith)
  refine ⟨result, source, related.1, resultSize, ?_⟩
  intro vector
  have kernels := model_kernel width rows rank column matrix previous size rankBound columnBound
    nonzero pivotNonzero prefixZero divides vector
  constructor
  · intro reduced
    apply kernels.mp
    intro row
    rw [← rowRelated row]
    exact reduced row
  · intro original
    have reduced := kernels.mpr original
    intro row
    rw [rowRelated row]
    exact reduced row

#print axioms eliminate_preserves

end Project.Beck.Elimination
