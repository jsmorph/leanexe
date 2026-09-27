import Project.Beck.MinorKernel

namespace Project.Beck.MinorHistory

open Matrix MinorState

variable {ι : Type} [Fintype ι] [DecidableEq ι] {width rows rank column : ℕ}

structure History (blocks : Blocks ι) (selected : ι → Fin width)
    (matrix : ℕ → ℕ → ℤ) (previous : ℤ) (columns : List UInt64) : Prop where
  determinant : previous = blocks.leading.det
  entries : ∀ row, rank ≤ row → row < rows → ∀ col : Fin width,
    matrix row col.val = minor blocks row col.val
  leading : ∀ i j, blocks.leading i j = blocks.top i (selected j).val
  left : ∀ row j, blocks.left row j = blocks.rest row (selected j).val
  chosen : ∀ word, word ∈ columns ↔ ∃ i, (selected i).val.toUInt64 = word
  before : ∀ i, (selected i).val < column
  injective : Function.Injective selected
  kernel : ∀ vector : Fin width → ℚ,
    (∀ i, ∑ col, (blocks.top i col.val : ℚ) * vector col = 0) ↔
      (∀ row, row < rank → ∑ col, (matrix row col.val : ℚ) * vector col = 0)

theorem initial (matrix : ℕ → ℕ → ℤ) :
    History (rows := rows) (rank := 0) (column := 0) (MinorState.initial matrix)
      (Fin.elim0 : Fin 0 → Fin width) matrix 1 [] := by
  refine ⟨(initial_det matrix).symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row _ _ col
    exact (initial_minor matrix row col.val).symm
  · intro i
    exact Fin.elim0 i
  · intro _ i
    exact Fin.elim0 i
  · intro word
    simp
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro vector
    simp

theorem skip (blocks : Blocks ι) (selected : ι → Fin width)
    (matrix : ℕ → ℕ → ℤ) (previous : ℤ) (columns : List UInt64)
    (history : History (rows := rows) (rank := rank) (column := column)
      blocks selected matrix previous columns) :
    History (rows := rows) (rank := rank) (column := column + 1)
      blocks selected matrix previous columns :=
  { history with before := fun i => Nat.lt_succ_of_lt (history.before i) }

theorem swapped (blocks : Blocks ι) (selected : ι → Fin width)
    (matrix next : ℕ → ℕ → ℤ) (previous : ℤ) (columns : List UInt64)
    (history : History (rows := rows) (rank := rank) (column := column)
      blocks selected matrix previous columns)
    (other : ℕ) (lower : rank ≤ other) (upper : other < rows)
    (entry : ∀ row, row < rows → ∀ col : Fin width,
      next row col.val = matrix (Equiv.swap rank other row) col.val) :
    History (rows := rows) (rank := rank) (column := column)
      (MinorState.swap blocks rank other) selected next previous columns := by
  have active (row : ℕ) (lo : rank ≤ row) (hi : row < rows) :
      rank ≤ Equiv.swap rank other row ∧ Equiv.swap rank other row < rows := by
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  have fixed (row : ℕ) (before : row < rank) : Equiv.swap rank other row = row := by
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega
  refine ⟨history.determinant, ?_, history.leading, ?_, history.chosen,
    history.before, history.injective, ?_⟩
  · intro row lo hi col
    rw [entry row hi col, MinorState.swap_minor]
    exact history.entries _ (active row lo hi).1 (active row lo hi).2 col
  · intro row j
    exact history.left _ j
  · intro vector
    change (∀ i, ∑ col, (blocks.top i col.val : ℚ) * vector col = 0) ↔ _
    rw [history.kernel vector]
    have same (row : ℕ) (before : row < rank) :
        (∑ col : Fin width, (next row col.val : ℚ) * vector col) =
          ∑ col : Fin width, (matrix row col.val : ℚ) * vector col := by
      apply Finset.sum_congr rfl
      intro col _
      rw [entry row (by omega) col, fixed row before]
    exact forall_congr' (fun row => forall_congr' (fun before => by rw [same row before]))

theorem extended (blocks : Blocks ι) (selected : ι → Fin width)
    (matrix next : ℕ → ℕ → ℤ) (previous : ℤ) (columns : List UInt64)
    (history : History (rows := rows) (rank := rank) (column := column)
      blocks selected matrix previous columns)
    (rankBound : rank < rows) (columnBound : column < width) (nonzero : previous ≠ 0)
    (unchanged : ∀ row, row ≤ rank → ∀ col : Fin width, next row col.val = matrix row col.val)
    (update : ∀ row, rank < row → row < rows → ∀ col : Fin width,
      previous * next row col.val = matrix rank column * matrix row col.val -
        matrix row column * matrix rank col.val) :
    History (rows := rows) (rank := rank + 1) (column := column + 1)
      (MinorState.extend blocks rank column)
      (Sum.elim selected (fun _ : Fin 1 => ⟨column, columnBound⟩))
      next (matrix rank column) (columns ++ [column.toUInt64]) := by
  have detNonzero : blocks.leading.det ≠ 0 := history.determinant ▸ nonzero
  have pivot : matrix rank column = minor blocks rank column :=
    history.entries rank le_rfl rankBound ⟨column, columnBound⟩
  refine ⟨pivot, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row lo hi col
    apply mul_left_cancel₀ detNonzero
    rw [MinorState.condensation _ _ _ _ _ detNonzero, ← history.determinant,
      update row (by omega) hi col, pivot,
      history.entries row (by omega) hi col,
      history.entries row (by omega) hi ⟨column, columnBound⟩,
      history.entries rank le_rfl rankBound col]
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact history.leading i j
    · rfl
    · exact history.left rank j
    · rfl
  · intro row j
    rcases j with j | j
    · exact history.left row j
    · rfl
  · intro word
    simp only [List.mem_append, history.chosen, List.mem_singleton, Sum.exists,
      Sum.elim_inl, Sum.elim_inr]
    simp only [exists_const]
    exact or_congr Iff.rfl eq_comm
  · intro i
    rcases i with i | i
    · exact Nat.lt_succ_of_lt (history.before i)
    · exact Nat.lt_succ_self _
  · intro i j equal
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (history.injective equal)
    · have valEqual := congrArg Fin.val equal
      have := history.before i
      simp only [Sum.elim_inl, Sum.elim_inr] at valEqual
      omega
    · have valEqual := congrArg Fin.val equal
      have := history.before j
      simp only [Sum.elim_inl, Sum.elim_inr] at valEqual
      omega
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  · intro vector
    have pivotSum (top : ∀ i, ∑ col, (blocks.top i col.val : ℚ) * vector col = 0) :
        (∑ col, (matrix rank col.val : ℚ) * vector col) =
          (previous : ℚ) * ∑ col, (blocks.rest rank col.val : ℚ) * vector col := by
      simp_rw [history.entries rank le_rfl rankBound]
      rw [MinorKernel.row_sum blocks rank vector detNonzero top, history.determinant]
    have previousNonzero : (previous : ℚ) ≠ 0 := by exact_mod_cast nonzero
    constructor
    · intro top row before
      have oldTop (i : ι) := top (Sum.inl i)
      have last := top (Sum.inr (0 : Fin 1))
      change (∑ col, (blocks.rest rank col.val : ℚ) * vector col) = 0 at last
      simp_rw [unchanged row (by omega)]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with earlier | rfl
      · exact (history.kernel vector).mp oldTop row earlier
      · rw [pivotSum oldTop, last, mul_zero]
    · intro sums
      have oldTop : ∀ i, ∑ col, (blocks.top i col.val : ℚ) * vector col = 0 := by
        apply (history.kernel vector).mpr
        intro row before
        have equation := sums row (by omega)
        simpa only [unchanged row (by omega)] using equation
      intro i
      rcases i with i | i
      · exact oldTop i
      · have equation := sums rank (by omega)
        simp_rw [unchanged rank le_rfl] at equation
        rw [pivotSum oldTop] at equation
        exact (mul_eq_zero.mp equation).resolve_left previousNonzero

#print axioms extended

end Project.Beck.MinorHistory
