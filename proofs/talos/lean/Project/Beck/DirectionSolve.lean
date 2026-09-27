import Project.Beck.Echelon
import Project.Beck.BackSubstitution

namespace Project.Beck.DirectionSolve

open LeanExe.Examples.BeckExact IntegerAdd Elimination BackSubstitution

def backward (width : ℕ) (basis : Echelon) (free : ℕ) : Option (Array Integer) :=
  forIn (List.range basis.columns.size)
    ((Array.replicate width Integer.zero).set! free basis.determinant)
    (backwardBody width basis.matrix basis.columns)

theorem source_eq (input : LeanExe.Examples.Beck.Input) (point : Point) (basis : Echelon)
    (source : echelon input.jobs (protectedMatrix input point) = some basis) :
    direction input point =
      if freeColumn input point basis.columns == input.jobs then none
      else backward input.jobs basis (freeColumn input point basis.columns) := by
  rw [direction, source]
  change ((pure basis : Option Echelon) >>= _) = _
  rw [pure_bind]
  dsimp only
  split_ifs
  · rfl
  · simp only [backward, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      ← List.range_eq_range', bind_assoc, bind_pure]
    congr 1
    funext offset vector
    simp only [backwardBody, step, addProduct, bind_assoc, pure_bind]

theorem backward_correct (width rows : ℕ) (matrix : Array Integer) (basis : Echelon)
    (invariant : EchelonProof.Invariant width rows width matrix basis)
    (fits : width ≤ UInt64.size) (free : Fin width)
    (notPivot : free.val.toUInt64 ∉ basis.columns) :
    ∃ result, backward width basis free.val = some result ∧
      (∀ entry ∈ result, Valid entry) ∧ result.size = width ∧
      value result[free.val]! = value basis.determinant ∧
      (∀ col : Fin width, col ≠ free → col.val.toUInt64 ∉ basis.columns → value result[col.val]! = 0) ∧
      (∀ row : Fin rows, ∑ col : Fin width,
        value matrix[row.val * width + col.val]! * value result[col.val]! = 0) := by
  obtain ⟨witness, freeValue, otherValue, pivotRows, originalRows⟩ :=
    EchelonProof.integer_kernel width rows matrix basis invariant free notPivot
  let answer : ℕ → ℤ := fun job => if inside : job < width then witness ⟨job, inside⟩ else 0
  have answerValue (col : Fin width) : answer col.val = witness col := by simp [answer, col.isLt]
  let initial := (Array.replicate width Integer.zero).set! free.val basis.determinant
  have initialValid : ∀ entry ∈ initial, Valid entry := by
    intro entry member
    rcases Array.mem_or_eq_of_mem_setIfInBounds member with old | equal
    · have : entry = Integer.zero := Array.eq_of_mem_replicate old
      simpa [this] using zero_correct.1
    · simpa [equal] using invariant.1.previousValid
  have initialSize : initial.size = width := by simp [initial]
  have agrees : Agrees width basis.columns.size basis.columns answer initial := by
    intro job inside absent
    by_cases same : job = free.val
    · subst job
      rw [Array.getElem!_set!_self _ _ _ (by simpa using free.isLt), answerValue free, freeValue]
    · have notSelected : job.toUInt64 ∉ basis.columns := by
        intro member
        obtain ⟨row, rowBound, equal⟩ := Array.mem_iff_getElem.mp member
        have valueEq := congrArg UInt64.toNat equal
        have encoded : job.toUInt64.toNat = job := by
          simp [Nat.toUInt64, Nat.mod_eq_of_lt (lt_of_lt_of_le inside fits)]
        rw [encoded] at valueEq
        exact absent row rowBound (by simpa only [getElem!_pos basis.columns row rowBound] using valueEq)
      have zero := otherValue ⟨job, inside⟩ (by intro equal; exact same (congrArg Fin.val equal)) notSelected
      rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm same),
        getElem!_pos (Array.replicate width Integer.zero) job (by simpa using inside),
        Array.getElem_replicate, zero_correct.2, answerValue ⟨job, inside⟩, zero]
  have equations (row : ℕ) (before : row < basis.columns.size) :
      ((List.range width).map (fun col => value basis.matrix[row * width + col]! * answer col)).sum = 0 := by
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]
    simp_rw [answerValue]
    exact pivotRows row before
  have matrixValid (row : ℕ) (before : row < basis.columns.size) (col : ℕ) (inside : col < width) :
      Valid basis.matrix[row * width + col]! := by
    apply get_valid _ invariant.1.valid
    rw [invariant.1.size]
    have rankBound := invariant.1.rankBound
    nlinarith
  obtain ⟨result, source, valid, size, recovered⟩ := backward_loop width basis.columns.size 0
    basis.matrix initial basis.columns answer (invariant.1.pivots fits) matrixValid initialValid initialSize
    equations (by omega) agrees
  have values (col : Fin width) : value result[col.val]! = witness col := by
    rw [← answerValue col]
    exact recovered col.val col.isLt (by omega)
  refine ⟨result, ?_, valid, size, by rw [values free, freeValue], ?_, ?_⟩
  · simpa only [backward, List.range_eq_range'] using source
  · intro col distinct absent
    rw [values col, otherValue col distinct absent]
  · intro row
    simp_rw [values]
    exact originalRows row

#print axioms backward_correct

end Project.Beck.DirectionSolve
