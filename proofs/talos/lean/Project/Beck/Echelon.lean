import Project.Beck.ActiveMatrix
import Project.Beck.Pivot

namespace Project.Beck.EchelonProof

open LeanExe.Examples.BeckExact IntegerAdd Elimination

def SameKernel (width rows : ℕ) (first second : Array Integer) : Prop :=
  ∀ vector : Fin width → ℚ,
    (∀ row : Fin rows, ∑ col, rationalRow width first row.val col * vector col = 0) ↔
      (∀ row : Fin rows, ∑ col, rationalRow width second row.val col * vector col = 0)

def Invariant (width rows column : ℕ) (initial : Array Integer) (state : Echelon) : Prop :=
  ActiveMatrix.Invariant width rows state.columns.size column state.matrix state.determinant ∧
    SameKernel width rows state.matrix initial

def body (width rows column : ℕ) (state : Echelon) : Option (ForInStep Echelon) := do
  let rank := state.columns.size
  let row := pivotRow width rows rank column state.matrix
  if row < rows then
    let swapped := swapRows width rank row state.matrix
    let pivot := swapped[rank * width + column]!
    let reduced ← eliminate width rows rank column swapped state.determinant
    return .yield ⟨reduced, state.columns.push column.toUInt64, pivot⟩
  else return .yield state

theorem source_eq (width : ℕ) (matrix : Array Integer) :
    echelon width matrix = forIn (List.range width)
      (Echelon.mk matrix #[] (Integer.ofWord 1)) (body width (matrix.size / width)) := by
  simp only [echelon, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp only [bind_pure]
  rfl

theorem step_correct (width rows column : ℕ) (initial : Array Integer) (state : Echelon)
    (invariant : Invariant width rows column initial state) (columnBound : column < width) :
    ∃ result, body width rows column state = some (.yield result) ∧
      Invariant width rows (column + 1) initial result := by
  let rank := state.columns.size
  let row := pivotRow width rows rank column state.matrix
  have pivotFacts := Pivot.pivot_correct width rows rank column state.matrix invariant.1.rankBound
  change rank ≤ row ∧ row ≤ rows ∧
    (row < rows → value state.matrix[row * width + column]! ≠ 0) ∧
    (∀ r, rank ≤ r → r < row → value state.matrix[r * width + column]! = 0) at pivotFacts
  by_cases found : row < rows
  · have rankBound : rank < rows := by omega
    let swapped := swapRows width rank row state.matrix
    have swappedInv := ActiveMatrix.swapped width rows rank column row state.matrix state.determinant
      invariant.1 pivotFacts.1 found
    have pivotNonzero : value swapped[rank * width + column]! ≠ 0 := by
      have entry := RowSwap.get_eq width rank row rank column state.matrix columnBound
        (by rw [invariant.1.size]; nlinarith)
      change value (swapRows width rank row state.matrix)[rank * width + column]! ≠ 0
      rw [entry, ite_eq_left rfl]
      exact pivotFacts.2.2.1 found
    obtain ⟨reduced, source, reducedInv⟩ := ActiveMatrix.eliminated width rows rank column swapped
      state.determinant swappedInv rankBound columnBound pivotNonzero
    have exactDivision := ActiveMatrix.divides width rows rank column swapped state.determinant
      swappedInv rankBound columnBound
    obtain ⟨sameReduced, sameSource, _, _, kernel⟩ := eliminate_preserves width rows rank column swapped
      state.determinant swappedInv.size rankBound columnBound swappedInv.valid swappedInv.previousValid
      swappedInv.nonzero pivotNonzero swappedInv.prefixZero exactDivision
    have same : sameReduced = reduced := Option.some.inj (sameSource.symm.trans source)
    subst sameReduced
    refine ⟨⟨reduced, state.columns.push column.toUInt64, swapped[rank * width + column]!⟩, ?_, ?_, ?_⟩
    · rw [body, ite_eq_left found]
      dsimp only
      rw [source]
      rfl
    · simpa only [Array.size_push] using reducedInv
    · intro vector
      exact (kernel vector).trans
        ((RowSwap.kernel width rows rank row state.matrix invariant.1.size rankBound found vector).trans
          (invariant.2 vector))
  · have absent : row = rows := by omega
    refine ⟨state, ?_, ?_, invariant.2⟩
    · rw [body, ite_eq_right found]
      rfl
    · exact ActiveMatrix.skip width rows rank column state.matrix state.determinant invariant.1
        columnBound (by intro r lower upper; exact pivotFacts.2.2.2 r lower (by omega))

theorem loop_correct (width rows count column : ℕ) (initial : Array Integer) (state : Echelon)
    (invariant : Invariant width rows column initial state) (bound : column + count ≤ width) :
    ∃ result, forIn (List.range' column count) state (body width rows) = some result ∧
      Invariant width rows (column + count) initial result := by
  induction count generalizing column state with
  | zero => exact ⟨state, rfl, invariant⟩
  | succ count ih =>
    obtain ⟨middle, step, middleInv⟩ := step_correct width rows column initial state invariant (by omega)
    obtain ⟨result, rest, resultInv⟩ := ih (column + 1) middle middleInv (by omega)
    refine ⟨result, ?_, by convert resultInv using 1 <;> omega⟩
    simpa only [List.range'_succ, List.forIn_cons, step, bind, pure, Option.bind] using rest

theorem echelon_correct (width rows : ℕ) (matrix : Array Integer)
    (widthPositive : 0 < width) (size : matrix.size = rows * width)
    (valid : ∀ entry ∈ matrix, Valid entry) :
    ∃ result, echelon width matrix = some result ∧ Invariant width rows width matrix result := by
  have start : Invariant width rows 0 matrix (Echelon.mk matrix #[] (Integer.ofWord 1)) :=
    ⟨ActiveMatrix.initial width rows matrix size valid, fun _ => Iff.rfl⟩
  obtain ⟨result, source, invariant⟩ := loop_correct width rows width 0 matrix _ start (by omega)
  refine ⟨result, ?_, by simpa only [Nat.zero_add] using invariant⟩
  rw [source_eq, size, Nat.mul_div_cancel _ widthPositive, List.range_eq_range']
  exact source

theorem kernel_of_pivot_rows (width rows : ℕ) (initial : Array Integer) (state : Echelon)
    (invariant : Invariant width rows width initial state) (vector : Fin width → ℚ)
    (pivots : ∀ row, row < state.columns.size →
      ∑ col, rationalRow width state.matrix row col * vector col = 0) :
    ∀ row : Fin rows, ∑ col, rationalRow width initial row.val col * vector col = 0 := by
  apply (invariant.2 vector).mp
  intro row
  by_cases selected : row.val < state.columns.size
  · exact pivots row.val selected
  · apply Finset.sum_eq_zero
    intro col _
    have zero := invariant.1.prefixZero row.val (by omega) row.isLt col.val col.isLt
    simp only [rationalRow, zero, Int.cast_zero, zero_mul]

#print axioms echelon_correct

end Project.Beck.EchelonProof
