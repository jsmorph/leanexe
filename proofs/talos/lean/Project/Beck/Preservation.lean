import Project.Beck.Minor
import Project.Beck.Sparse

namespace Project.Beck.Preservation

open LeanExe.Examples.Beck

def entry (input : Input) (x : Point) (row col : Nat) : ℚ :=
  Arithmetic.value (protectedMatrix input x)[row * input.jobs + col]!

theorem bordered_zero (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (positive : 0 < input.jobs) (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (rank : basis.rows.size ≤ 5)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (maximal : Basis.extension input.jobs (protectedMatrix input x) basis = none)
    (row col : Nat) (hr : row < (protectedMatrix input x).size / input.jobs) (hc : col < input.jobs)
    (freshRow : row.toUInt64 ∉ basis.rows) (freshCol : col.toUInt64 ∉ basis.columns) :
    (Cofactors.border (Minor.rational basis.rows.size input.jobs (protectedMatrix input x) basis.rows basis.columns)
      (fun i => entry input x basis.rows[i.val]!.toNat col.toUInt64.toNat)
      (fun j => entry input x row.toUInt64.toNat basis.columns[j.val]!.toNat)
      (entry input x row.toUInt64.toNat col.toUInt64.toNat)).det = 0 := by
  have ri := Basis.indices_push wf.rows row.toUInt64
    ((Nat.mod_le _ _).trans_lt hr) freshRow
  have ci := Basis.indices_push wf.columns col.toUInt64
    ((Nat.mod_le _ _).trans_lt hc) freshCol
  have binaryBorder := MatrixBasis.indices_binary input x (basis.rows.size + 1)
    (basis.rows.push row.toUInt64) (basis.columns.push col.toUInt64) positive ri ci
    (by simp) (by simp [wf.square]) binary
  unfold entry
  rw [show Cofactors.border _ _ _ _ =
    (Minor.rational (basis.rows.size + 1) input.jobs (protectedMatrix input x)
      (basis.rows.push row.toUInt64) (basis.columns.push col.toUInt64)).submatrix
      finSumFinEquiv finSumFinEquiv from
        (Minor.bordered _ _ _ _ _ rfl wf.square.symm _ _).symm,
    Matrix.det_submatrix_equiv_self,
    ← Minor.determinant_rational _ _ _ _ _ (by simp) (by simp [wf.square]) (by omega) binaryBorder,
    Basis.maximal_border_zero _ _ _ _ _ maximal hr hc freshRow freshCol]
  rfl

theorem assemble_preserves (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (capacity : input.jobs ≤ 6)
    (short : (protectedMatrix input x).size / input.jobs < input.jobs)
    (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (rank : basis.rows.size ≤ 5)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (maximal : Basis.extension input.jobs (protectedMatrix input x) basis = none)
    (row : Nat) (hr : row < (protectedMatrix input x).size / input.jobs)
    (free : Fin input.jobs) (fresh : free.val.toUInt64 ∉ basis.columns) :
    (∑ job : Fin input.jobs, entry input x row job.val *
      (Arithmetic.value (Direction.assemble input.jobs (protectedMatrix input x) basis free.val)[job.val]! : ℚ)) = 0 := by
  have positive : 0 < input.jobs := (Nat.zero_le free.val).trans_lt free.isLt
  have freeExact : free.val.toUInt64.toNat = free.val := by
    change free.val % 18446744073709551616 = free.val
    apply Nat.mod_eq_of_lt
    omega
  have rowExact : row.toUInt64.toNat = row := by
    change row % 18446744073709551616 = row
    apply Nat.mod_eq_of_lt
    omega
  let A := Minor.rational basis.rows.size input.jobs (protectedMatrix input x) basis.rows basis.columns
  let b := fun i : Fin basis.rows.size => entry input x basis.rows[i.val]!.toNat free.val
  have detEq : (Arithmetic.value basis.determinant : ℚ) = A.det :=
    Minor.basis_det input x basis positive wf rank binary
  have nonzero : A.det ≠ 0 := by
    rw [← detEq]
    exact_mod_cast (Determinant.value_ne_zero basis.determinant).mpr wf.nonzero
  have coefficientEq (j : Fin basis.rows.size) :
      (Arithmetic.value (Direction.coefficient input.jobs (protectedMatrix input x) basis free.val j.val) : ℚ) =
        -A.cramer b j := by
    simpa only [A, b, entry, freeExact] using Minor.coefficient_rational input x basis positive wf rank binary
      free.val free.isLt j
  rw [Sparse.assemble_sum _ _ _ wf.columns free fresh]
  simp only [Sparse.columnIndex]
  have sumEq (f : Nat → ℚ) : (∑ j : Fin basis.columns.size, f j.val) =
      ∑ j : Fin basis.rows.size, f j.val := by
    rw [← Finset.sum_range, ← wf.square, Finset.sum_range]
  rw [sumEq (fun j => entry input x row basis.columns[j]!.toNat *
    (Arithmetic.value (Direction.coefficient input.jobs (protectedMatrix input x) basis free.val j) : ℚ)), detEq]
  simp_rw [coefficientEq]
  rw [add_comm]
  by_cases selected : row.toUInt64 ∈ basis.rows
  · obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp selected
    have rowAt : basis.rows[i]!.toNat = row := by
      rw [getElem!_pos basis.rows i hi, he, rowExact]
    have result := Cofactors.selected_row_preserved A b (⟨i, hi⟩ : Fin basis.rows.size)
    simpa only [A, b, Minor.rational, Matrix.map_apply, Determinant.minor, entry, rowAt] using result
  · have borderZero := bordered_zero input x basis positive wf rank binary maximal row free.val hr free.isLt selected fresh
    simp only [rowExact, freeExact] at borderZero
    exact Cofactors.other_row_preserved A b (fun j => entry input x row basis.columns[j.val]!.toNat)
      (entry input x row free.val) nonzero borderZero

theorem direction_preserves_row (input : Input) (x : Point)
    (capacity : input.jobs ≤ 6)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ Counting.members input category).card ≤ input.overlap)
    (nonempty : (Counting.live input x).Nonempty)
    (row : Nat) (hr : row < (protectedMatrix input x).size / input.jobs) :
    (∑ job : Fin input.jobs, entry input x row job.val *
      (Arithmetic.value (direction input x)[job.val]! : ℚ)) = 0 := by
  have basis := ProtectedMatrix.source_basis_complete input x overlap nonempty
  have free := FreeColumn.source_freeColumn input x capacity overlap nonempty
  have rank : (Direction.sourceBasis input x).rows.size ≤ 5 := by
    have bound : (Direction.sourceBasis input x).rows.size < input.jobs := basis.2.2
    omega
  rw [Direction.direction_eq input x free.1]
  exact assemble_preserves input x _ capacity (ProtectedMatrix.protectedMatrix_short input x overlap nonempty)
    basis.1 rank binary basis.2.1 row hr ⟨_, free.1⟩ free.2.2

theorem direction_preserves_category (input : Input) (x : Point)
    (capacity : input.jobs ≤ 6)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ Counting.members input category).card ≤ input.overlap)
    (nonempty : (Counting.live input x).Nonempty)
    (category : Fin input.categories) (protectedCount : input.overlap < liveCount input x category.val) :
    (∑ job ∈ Counting.members input category, (Arithmetic.value (direction input x)[job.val]! : ℚ)) = 0 := by
  have member : category.val ∈ ProtectedMatrix.selected input x := by
    simp [ProtectedMatrix.selected, category.isLt, protectedCount]
  obtain ⟨row, hr, he⟩ := List.mem_iff_getElem.mp member
  have positive : 0 < input.jobs := by
    obtain ⟨job, _⟩ := nonempty
    exact (Nat.zero_le job.val).trans_lt job.isLt
  have rowBound : row < (protectedMatrix input x).size / input.jobs := by
    rwa [MatrixBasis.row_count input x positive]
  have result := direction_preserves_row input x capacity binary overlap nonempty row rowBound
  rw [← result, Counting.members, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro job _
  unfold entry
  rw [ProtectedMatrix.protectedMatrix_get input x row job.val hr job.isLt, he]
  by_cases hf : frozen x job.val = true
  · rw [Direction.direction_frozen_zero input x capacity overlap nonempty job.val job.isLt hf]
    simp [Arithmetic.value]
  · have live : frozen x job.val = false := Bool.eq_false_iff.mpr hf
    rcases binary job.val job.isLt category.val category.isLt with zero | one
    · simp [live, zero, Arithmetic.value]
    · simp [live, one, Arithmetic.value]

end Project.Beck.Preservation
