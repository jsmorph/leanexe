import Project.Beck.MinorHistory
import Project.Beck.RowSwap

namespace Project.Beck.ActiveMatrix

open LeanExe.Examples.BeckExact IntegerAdd Elimination

structure Invariant (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (columns : List UInt64) : Prop where
  size : matrix.size = rows * width
  valid : ∀ entry ∈ matrix, Valid entry
  previousValid : Valid previous
  rankBound : rank ≤ rows
  columnBound : column ≤ width
  nonzero : value previous ≠ 0
  prefixZero : ∀ row, rank ≤ row → row < rows → ∀ col, col < column →
    value matrix[row * width + col]! = 0
  history : ∃ (ι : Type) (finite : Fintype ι) (decidable : DecidableEq ι)
      (blocks : MinorState.Blocks ι) (selected : ι → Fin width),
    let _ := finite
    let _ := decidable
    MinorHistory.History (rows := rows) (rank := rank) (column := column)
      blocks selected (fun row col => value matrix[row * width + col]!) (value previous) columns

theorem initial (width rows : ℕ) (matrix : Array Integer)
    (size : matrix.size = rows * width) (valid : ∀ entry ∈ matrix, Valid entry) :
    Invariant width rows 0 0 matrix (Integer.ofWord 1) [] := by
  have one := IntegerOrder.ofWord_correct 1
  refine ⟨size, valid, one.1, Nat.zero_le _, Nat.zero_le _, by simp [one.2], by omega, ?_⟩
  refine ⟨Fin 0, inferInstance, inferInstance,
    MinorState.initial (fun row col => value matrix[row * width + col]!), Fin.elim0, ?_⟩
  simpa [one.2] using MinorHistory.initial (rows := rows) (width := width)
    (fun row col => value matrix[row * width + col]!)

theorem skip (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (columns : List UInt64) (invariant : Invariant width rows rank column matrix previous columns)
    (columnBound : column < width)
    (zero : ∀ row, rank ≤ row → row < rows → value matrix[row * width + column]! = 0) :
    Invariant width rows rank (column + 1) matrix previous columns := by
  refine { invariant with columnBound := by omega, prefixZero := ?_, history := ?_ }
  · intro row lower upper col before
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with lt | rfl
    · exact invariant.prefixZero row lower upper col lt
    · exact zero row lower upper
  · obtain ⟨ι, finite, decidable, blocks, selected, history⟩ := invariant.history
    exact ⟨ι, finite, decidable, blocks, selected, MinorHistory.skip _ _ _ _ _ history⟩

theorem swapped (width rows rank column other : ℕ) (matrix : Array Integer) (previous : Integer)
    (columns : List UInt64) (invariant : Invariant width rows rank column matrix previous columns)
    (lower : rank ≤ other) (upper : other < rows) :
    Invariant width rows rank column (swapRows width rank other matrix) previous columns := by
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
  · obtain ⟨ι, finite, decidable, blocks, selected, history⟩ := invariant.history
    let _ := finite
    let _ := decidable
    refine ⟨ι, finite, decidable, MinorState.swap blocks rank other, selected, ?_⟩
    exact MinorHistory.swapped _ _ _ _ _ _ history other lower upper
      (by intro row inside col; rw [entry row col.val inside col.isLt])

theorem divides (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (columns : List UInt64) (invariant : Invariant width rows rank column matrix previous columns)
    (rankBound : rank < rows) (columnBound : column < width) :
    ∀ row, rank < row → row < rows → ∀ col, column < col → col < width →
      value previous ∣ value matrix[rank * width + column]! * value matrix[row * width + col]! -
        value matrix[row * width + column]! * value matrix[rank * width + col]! := by
  obtain ⟨ι, finite, decidable, blocks, selected, history⟩ := invariant.history
  let _ := finite
  let _ := decidable
  intro row lower upper col afterColumn colBound
  rw [history.determinant, history.entries rank le_rfl rankBound ⟨column, columnBound⟩,
    history.entries row (by omega) upper ⟨col, colBound⟩,
    history.entries row (by omega) upper ⟨column, columnBound⟩,
    history.entries rank le_rfl rankBound ⟨col, colBound⟩]
  exact MinorState.divides blocks rank column row col
    (by simpa [← history.determinant] using invariant.nonzero)

theorem eliminated (width rows rank column : ℕ) (matrix : Array Integer) (previous : Integer)
    (columns : List UInt64) (invariant : Invariant width rows rank column matrix previous columns)
    (rankBound : rank < rows) (columnBound : column < width)
    (pivotNonzero : value matrix[rank * width + column]! ≠ 0) :
    ∃ result, eliminate width rows rank column matrix previous = some result ∧
      Invariant width rows (rank + 1) (column + 1) result matrix[rank * width + column]!
        (columns ++ [column.toUInt64]) := by
  have exactDivision := divides width rows rank column matrix previous columns invariant rankBound columnBound
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
  · obtain ⟨ι, finite, decidable, blocks, selected, history⟩ := invariant.history
    let _ := finite
    let _ := decidable
    refine ⟨ι ⊕ Fin 1, inferInstance, inferInstance, MinorState.extend blocks rank column,
      Sum.elim selected (fun _ : Fin 1 => ⟨column, columnBound⟩), ?_⟩
    apply MinorHistory.extended _ _ _ _ _ _ history rankBound columnBound invariant.nonzero
    · intro row before col
      rw [entry row col.val (by omega) col.isLt, ite_eq_right (by omega)]
    · intro row lower upper col
      rw [entry row col.val upper col.isLt, ite_eq_left lower]
      by_cases afterColumn : column < col.val
      · rw [ite_eq_left afterColumn, entryValue,
          Int.mul_ediv_cancel' (exactDivision row lower upper col.val afterColumn col.isLt)]
      · rw [ite_eq_right afterColumn]
        by_cases sameColumn : col.val = column
        · simp [sameColumn, mul_comm]
        · have earlier : col.val < column := by omega
          rw [ite_eq_right sameColumn,
            invariant.prefixZero row (by omega) upper col.val earlier,
            invariant.prefixZero rank le_rfl rankBound col.val earlier]
          ring

#print axioms eliminated

end Project.Beck.ActiveMatrix
