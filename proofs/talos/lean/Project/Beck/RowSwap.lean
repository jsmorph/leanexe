import Project.Beck.EliminationKernel

namespace Project.Beck.RowSwap

open LeanExe.Examples.BeckExact IntegerAdd Elimination

def updates (width first second : ℕ) (matrix : Array Integer) : List (ℕ × Integer) :=
  (List.range width).flatMap fun col =>
    [(first * width + col, matrix[second * width + col]!),
      (second * width + col, matrix[first * width + col]!)]

theorem source_eq (width first second : ℕ) (matrix : Array Integer) (distinct : first ≠ second) :
    swapRows width first second matrix =
      (updates width first second matrix).foldl (fun result item => result.set! item.1 item.2) matrix := by
  simp only [swapRows, beq_iff_eq, distinct, ite_false,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  change (forIn (List.range width) matrix (fun column result =>
    pure (ForInStep.yield ((result.set! (first * width + column)
      matrix[second * width + column]!).set! (second * width + column)
      matrix[first * width + column]!))) : Id (Array Integer)) = _
  rw [List.forIn_pure_yield_eq_foldl]
  rw [updates, List.foldl_flatMap]
  rfl

theorem size_eq (width first second : ℕ) (matrix : Array Integer) :
    (swapRows width first second matrix).size = matrix.size := by
  by_cases equal : first = second
  · simp [swapRows, equal]
  · rw [source_eq width first second matrix equal]
    exact fold_set_size _ Prod.fst Prod.snd matrix

theorem get_eq (width first second row col : ℕ) (matrix : Array Integer)
    (colBound : col < width) (inside : row * width + col < matrix.size) :
    (swapRows width first second matrix)[row * width + col]! =
      matrix[(if row = first then second else if row = second then first else row) * width + col]! := by
  classical
  by_cases distinct : first = second
  · simp only [swapRows, distinct, beq_self_eq_true, ↓reduceIte]
    by_cases equal : row = second <;> simp [equal]
  · rw [source_eq width first second matrix distinct]
    have member (item : ℕ × Integer) : item ∈ updates width first second matrix ↔
        ∃ c < width, item = (first * width + c, matrix[second * width + c]!) ∨
          item = (second * width + c, matrix[first * width + c]!) := by
      simp [updates, List.mem_flatMap]
    have found : (∃ item ∈ updates width first second matrix, item.1 = row * width + col) ↔
        row = first ∨ row = second := by
      constructor
      · rintro ⟨item, hmem, equal⟩
        obtain ⟨c, hc, rfl | rfl⟩ := (member item).mp hmem
        · exact Or.inl (flat_unique width first row c col hc colBound equal).1.symm
        · exact Or.inr (flat_unique width second row c col hc colBound equal).1.symm
      · rintro (rfl | rfl)
        · exact ⟨_, (member _).mpr ⟨col, colBound, Or.inl rfl⟩, rfl⟩
        · exact ⟨_, (member _).mpr ⟨col, colBound, Or.inr rfl⟩, rfl⟩
    have result := fold_set_get (updates width first second matrix) Prod.fst Prod.snd matrix
      (row * width + col) inside
      matrix[(if row = first then second else if row = second then first else row) * width + col]!
      (by
        intro item hmem equal
        obtain ⟨c, hc, rfl | rfl⟩ := (member item).mp hmem
        · have unique := flat_unique width first row c col hc colBound equal
          simp [← unique.1, unique.2]
        · have unique := flat_unique width second row c col hc colBound equal
          simp [← unique.1, unique.2, Ne.symm distinct])
    simp only [found] at result
    rw [result]
    by_cases left : row = first <;> by_cases right : row = second <;> simp [left, right]

theorem valid (width rows first second : ℕ) (matrix : Array Integer)
    (size : matrix.size = rows * width) (firstBound : first < rows) (secondBound : second < rows)
    (matrixValid : ∀ entry ∈ matrix, Valid entry) :
    ∀ entry ∈ swapRows width first second matrix, Valid entry := by
  intro entry member
  obtain ⟨index, inside, equal⟩ := Array.mem_iff_getElem.mp member
  have sourceInside : index < matrix.size := by simpa [size_eq] using inside
  have widthPositive : 0 < width := by rw [size] at sourceInside; nlinarith
  have rowBound : index / width < rows := (Nat.div_lt_iff_lt_mul widthPositive).mpr
    (by simpa [size, mul_comm] using sourceInside)
  have colBound : index % width < width := Nat.mod_lt _ widthPositive
  have recombine : index / width * width + index % width = index := by
    simpa [Nat.mul_comm] using Nat.div_add_mod index width
  have selected := get_eq width first second (index / width) (index % width) matrix
    colBound (by simpa [recombine] using sourceInside)
  rw [recombine, getElem!_pos (swapRows width first second matrix) index inside, equal] at selected
  rw [selected]
  apply get_valid matrix matrixValid
  rw [size]
  split_ifs <;> nlinarith

#print axioms get_eq
#print axioms valid

theorem row_eq (width rows first second row : ℕ) (matrix : Array Integer)
    (size : matrix.size = rows * width) (rowBound : row < rows) :
    rationalRow width (swapRows width first second matrix) row =
      rationalRow width matrix (Equiv.swap first second row) := by
  funext col
  simp only [rationalRow, Equiv.swap_apply_def]
  rw [get_eq width first second row col.val matrix col.isLt (by
    rw [size]
    have colBound := col.isLt
    nlinarith)]

theorem kernel (width rows first second : ℕ) (matrix : Array Integer)
    (size : matrix.size = rows * width) (firstBound : first < rows) (secondBound : second < rows)
    (vector : Fin width → ℚ) :
    (∀ row : Fin rows, ∑ col, rationalRow width (swapRows width first second matrix)
      row.val col * vector col = 0) ↔
    (∀ row : Fin rows, ∑ col, rationalRow width matrix row.val col * vector col = 0) := by
  have bound (row : ℕ) (inside : row < rows) : Equiv.swap first second row < rows := by
    simp only [Equiv.swap_apply_def]
    split_ifs <;> assumption
  constructor
  · intro swapped row
    have equation := swapped ⟨Equiv.swap first second row.val, bound row.val row.isLt⟩
    rw [row_eq width rows first second _ matrix size (bound row.val row.isLt)] at equation
    simpa using equation
  · intro original row
    rw [row_eq width rows first second row.val matrix size row.isLt]
    exact original ⟨Equiv.swap first second row.val, bound row.val row.isLt⟩

#print axioms kernel

end Project.Beck.RowSwap
