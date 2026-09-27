import Mathlib.Tactic

namespace Project.Beck.EchelonShape

structure Pivots (rank column : ℕ) (matrix : ℕ → ℕ → ℤ) (columns : List ℕ) : Prop where
  length : columns.length = rank
  before : ∀ row, row < rank → columns[row]! < column
  ordered : ∀ first second, first < second → second < rank → columns[first]! < columns[second]!
  nonzero : ∀ row, row < rank → matrix row columns[row]! ≠ 0
  leadingZero : ∀ row, row < rank → ∀ col, col < columns[row]! → matrix row col = 0

theorem initial (matrix : ℕ → ℕ → ℤ) : Pivots 0 0 matrix [] := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> omega

theorem skip {rank column : ℕ} {matrix : ℕ → ℕ → ℤ} {columns : List ℕ}
    (pivots : Pivots rank column matrix columns) : Pivots rank (column + 1) matrix columns :=
  { pivots with before := fun row inside => Nat.lt_succ_of_lt (pivots.before row inside) }

theorem transfer {rank column : ℕ} {matrix next : ℕ → ℕ → ℤ} {columns : List ℕ}
    (pivots : Pivots rank column matrix columns)
    (same : ∀ row, row < rank → ∀ col, col < column → next row col = matrix row col) :
    Pivots rank column next columns := by
  refine { pivots with nonzero := ?_, leadingZero := ?_ }
  · intro row inside
    rw [same row inside _ (pivots.before row inside)]
    exact pivots.nonzero row inside
  · intro row inside col before
    rw [same row inside col (lt_trans before (pivots.before row inside))]
    exact pivots.leadingZero row inside col before

theorem append_get (columns : List ℕ) (column row : ℕ) (inside : row < columns.length) :
    (columns ++ [column])[row]! = columns[row]! := by
  rw [getElem!_pos (columns ++ [column]) row (by simp; omega),
    List.getElem_append_left inside, getElem!_pos columns row inside]

theorem append_last (columns : List ℕ) (column : ℕ) :
    (columns ++ [column])[columns.length]! = column := by
  rw [getElem!_pos _ _ (by simp), List.getElem_append_right (by omega)]
  simp

theorem push {rank column : ℕ} {matrix next : ℕ → ℕ → ℤ} {columns : List ℕ}
    (pivots : Pivots rank column matrix columns)
    (same : ∀ row, row ≤ rank → ∀ col, col ≤ column → next row col = matrix row col)
    (nonzero : matrix rank column ≠ 0)
    (leadingZero : ∀ col, col < column → matrix rank col = 0) :
    Pivots (rank + 1) (column + 1) next (columns ++ [column]) := by
  have old (row : ℕ) (inside : row < rank) := append_get columns column row (by rw [pivots.length]; exact inside)
  have last : (columns ++ [column])[rank]! = column := by rw [← pivots.length, append_last]
  refine ⟨by simp [pivots.length], ?_, ?_, ?_, ?_⟩
  · intro row inside
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ inside) with before | rfl
    · rw [old row before]
      exact Nat.lt_succ_of_lt (pivots.before row before)
    · rw [last]
      omega
  · intro first second earlier inside
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ inside) with before | rfl
    · rw [old first (by omega), old second before]
      exact pivots.ordered first second earlier before
    · rw [old first earlier, last]
      exact pivots.before first earlier
  · intro row inside
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ inside) with before | rfl
    · rw [old row before, same row (by omega) _ (Nat.le_of_lt (pivots.before row before))]
      exact pivots.nonzero row before
    · rw [last, same _ le_rfl column le_rfl]
      exact nonzero
  · intro row inside col earlier
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ inside) with before | rfl
    · rw [old row before] at earlier
      rw [same row (by omega) col (by have := pivots.before row before; omega)]
      exact pivots.leadingZero row before col earlier
    · rw [last] at earlier
      rw [same _ le_rfl col (by omega)]
      exact leadingZero col earlier

end Project.Beck.EchelonShape
