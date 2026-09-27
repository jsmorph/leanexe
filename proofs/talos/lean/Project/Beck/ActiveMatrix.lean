import Project.Beck.MinorState
import Project.Beck.RowSwap

namespace Project.Beck.ActiveMatrix

open LeanExe.Examples.BeckExact IntegerAdd Elimination

structure Invariant (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer) : Prop where
  size : matrix.size = rows * width
  valid : ∀ entry ∈ matrix, Valid entry
  previousValid : Valid previous
  rankBound : rank ≤ rows
  columnBound : column ≤ width
  nonzero : value previous ≠ 0
  prefixZero : ∀ row, rank ≤ row → row < rows → ∀ col, col < column →
    value matrix[row * width + col]! = 0
  minors : ∃ (ι : Type) (finite : Fintype ι) (decidable : DecidableEq ι)
      (blocks : MinorState.Blocks ι),
    let _ := finite
    let _ := decidable
    value previous = blocks.leading.det ∧
    ∀ row, rank ≤ row → row < rows → ∀ col, column ≤ col → col < width →
      value matrix[row * width + col]! = MinorState.minor blocks row col

theorem initial (width rows : ℕ) (matrix : Array Integer)
    (size : matrix.size = rows * width) (valid : ∀ entry ∈ matrix, Valid entry) :
    Invariant width rows 0 0 matrix (Integer.ofWord 1) := by
  have one := IntegerOrder.ofWord_correct 1
  refine ⟨size, valid, one.1, Nat.zero_le _, Nat.zero_le _, by simp [one.2], by omega, ?_⟩
  refine ⟨Fin 0, inferInstance, inferInstance,
    MinorState.initial (fun row col => value matrix[row * width + col]!), ?_, ?_⟩
  · simp [one.2]
  · intro row _ _ col _ _
    rw [MinorState.initial_minor]

theorem skip (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (invariant : Invariant width rows rank column matrix previous)
    (columnBound : column < width)
    (zero : ∀ row, rank ≤ row → row < rows → value matrix[row * width + column]! = 0) :
    Invariant width rows rank (column + 1) matrix previous := by
  refine { invariant with columnBound := by omega, prefixZero := ?_, minors := ?_ }
  · intro row lower upper col before
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with lt | rfl
    · exact invariant.prefixZero row lower upper col lt
    · exact zero row lower upper
  · obtain ⟨ι, finite, decidable, blocks, determinant, entries⟩ := invariant.minors
    exact ⟨ι, finite, decidable, blocks, determinant,
      fun row lower upper col afterColumn colBound => entries row lower upper col (by omega) colBound⟩

theorem swapped (width rows rank column other : ℕ) (matrix : Array Integer) (previous : Integer)
    (invariant : Invariant width rows rank column matrix previous)
    (lower : rank ≤ other) (upper : other < rows) :
    Invariant width rows rank column (swapRows width rank other matrix) previous := by
  have rankBound : rank < rows := by omega
  have bounds (row : ℕ) (lo : rank ≤ row) (hi : row < rows) :
      rank ≤ Equiv.swap rank other row ∧ Equiv.swap rank other row < rows := by
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  have entry (row col : ℕ) (hr : row < rows) (hc : col < width) :
      (swapRows width rank other matrix)[row * width + col]! =
        matrix[Equiv.swap rank other row * width + col]! := by
    simpa only [Equiv.swap_apply_def] using RowSwap.get_eq width rank other row col matrix hc
      (by rw [invariant.size]; nlinarith)
  refine ⟨by rw [RowSwap.size_eq, invariant.size],
    RowSwap.valid width rows rank other matrix invariant.size rankBound upper invariant.valid,
    invariant.previousValid, invariant.rankBound, invariant.columnBound, invariant.nonzero, ?_, ?_⟩
  · intro row lo hi col before
    rw [entry row col hi (by have := invariant.columnBound; omega)]
    exact invariant.prefixZero _ (bounds row lo hi).1 (bounds row lo hi).2 col before
  · obtain ⟨ι, finite, decidable, blocks, determinant, entries⟩ := invariant.minors
    let _ := finite
    let _ := decidable
    refine ⟨ι, finite, decidable, MinorState.swap blocks rank other, determinant, ?_⟩
    intro row lo hi col afterColumn inside
    rw [entry row col hi inside, MinorState.swap_minor]
    exact entries _ (bounds row lo hi).1 (bounds row lo hi).2 col afterColumn inside

theorem divides (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (invariant : Invariant width rows rank column matrix previous)
    (rankBound : rank < rows) (columnBound : column < width) :
    ∀ row, rank < row → row < rows → ∀ col, column < col → col < width →
      value previous ∣ value matrix[rank * width + column]! * value matrix[row * width + col]! -
        value matrix[row * width + column]! * value matrix[rank * width + col]! := by
  obtain ⟨ι, finite, decidable, blocks, determinant, entries⟩ := invariant.minors
  let _ := finite
  let _ := decidable
  intro row lower upper col afterColumn colBound
  rw [determinant, entries rank le_rfl rankBound column le_rfl columnBound,
    entries row (by omega) upper col (by omega) colBound,
    entries row (by omega) upper column le_rfl columnBound,
    entries rank le_rfl rankBound col (by omega) colBound]
  exact MinorState.divides blocks rank column row col (by simpa [← determinant] using invariant.nonzero)

theorem eliminated (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (invariant : Invariant width rows rank column matrix previous)
    (rankBound : rank < rows) (columnBound : column < width)
    (pivotNonzero : value matrix[rank * width + column]! ≠ 0) :
    ∃ result, eliminate width rows rank column matrix previous = some result ∧
      Invariant width rows (rank + 1) (column + 1) result matrix[rank * width + column]! := by
  have exactDivision := divides width rows rank column matrix previous invariant rankBound columnBound
  obtain ⟨result, source, related⟩ := eliminate_correct width rows rank column matrix previous
    invariant.size rankBound columnBound invariant.valid invariant.previousValid invariant.nonzero exactDivision
  have size : result.size = matrix.size := by
    have equation := congrArg Array.size related.2
    simpa only [Array.size_map, model_size] using equation
  have entry (row col : ℕ) (hr : row < rows) (hc : col < width) :
      value result[row * width + col]! =
        if rank < row then
          if column < col then entryValue width rank column row col matrix previous
          else if col = column then 0 else value matrix[row * width + col]!
        else value matrix[row * width + col]! := by
    have inside : row * width + col < result.size := by rw [size, invariant.size]; nlinarith
    have mapped : value result[row * width + col]! = (result.map value)[row * width + col]! := by
      rw [getElem!_pos result _ inside,
        getElem!_pos (result.map value) _ (by simpa using inside), Array.getElem_map]
    rw [mapped, related.2]
    exact model_get width rows rank column row col matrix previous invariant.size rankBound columnBound hr hc
  refine ⟨result, source, by rw [size, invariant.size], related.1,
    get_valid matrix invariant.valid _ (by rw [invariant.size]; nlinarith),
    by omega, by omega, pivotNonzero, ?_, ?_⟩
  · intro row lower upper col before
    rw [entry row col upper (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
    split
    · rfl
    · exact invariant.prefixZero row (by omega) upper col (by omega)
  · obtain ⟨ι, finite, decidable, blocks, determinant, entries⟩ := invariant.minors
    let _ := finite
    let _ := decidable
    refine ⟨ι ⊕ Fin 1, inferInstance, inferInstance, MinorState.extend blocks rank column, ?_, ?_⟩
    · exact entries rank le_rfl rankBound column le_rfl columnBound
    · intro row lower upper col afterColumn colBound
      rw [entry row col upper colBound, ite_eq_left (by omega), ite_eq_left (by omega), entryValue,
        determinant, entries rank le_rfl rankBound column le_rfl columnBound,
        entries row (by omega) upper col (by omega) colBound,
        entries row (by omega) upper column le_rfl columnBound,
        entries rank le_rfl rankBound col (by omega) colBound]
      rw [← MinorState.condensation blocks rank column row col
        (by simpa [← determinant] using invariant.nonzero), Int.mul_ediv_cancel_left _
        (by simpa [← determinant] using invariant.nonzero)]

#print axioms eliminated

end Project.Beck.ActiveMatrix
