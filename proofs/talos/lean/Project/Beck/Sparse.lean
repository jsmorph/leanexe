import Project.Beck.Direction

namespace Project.Beck.Sparse

open LeanExe.Examples.Beck

def columnIndex {width : Nat} {columns : Array UInt64} (indices : Basis.Indices width columns)
    (j : Fin columns.size) : Fin width := ⟨columns[j.val]!.toNat, MatrixBasis.index_bound indices j.val j.isLt⟩

theorem columnIndex_injective {width : Nat} {columns : Array UInt64}
    (indices : Basis.Indices width columns) : Function.Injective (columnIndex indices) := by
  intro i j equal
  apply Fin.ext
  have values := congrArg (fun z : Fin width => z.val) equal
  change columns[i.val]!.toNat = columns[j.val]!.toNat at values
  have words : columns[i.val]! = columns[j.val]! := UInt64.toNat_inj.mp values
  rw [getElem!_pos columns i.val i.isLt, getElem!_pos columns j.val j.isLt] at words
  exact indices.nodup.eq_of_getElem_eq
    (by simp) (by simp) words

theorem sum_support {n k : Nat} (index : Fin k → Fin n) (injective : Function.Injective index)
    (free : Fin n) (fresh : ∀ i, index i ≠ free) (w d : Fin n → ℚ)
    (zero : ∀ j, j ≠ free → (∀ i, index i ≠ j) → d j = 0) :
    (∑ j, w j * d j) = w free * d free + ∑ i, w (index i) * d (index i) := by
  let selected := Finset.univ.image index
  have absent : free ∉ selected := by simpa [selected] using fresh
  have reduce : (∑ j, w j * d j) = ∑ j ∈ insert free selected, w j * d j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ outside
    simp only [Finset.mem_insert, not_or] at outside
    have unused : ∀ i, index i ≠ j := by simpa [selected] using outside.2
    simp [zero j outside.1 unused]
  rw [reduce, Finset.sum_insert absent]
  congr 1
  exact Finset.sum_image (by intro a _ b _ equal; exact injective equal)

theorem assemble_sum (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis)
    (indices : Basis.Indices width basis.columns) (free : Fin width)
    (fresh : free.val.toUInt64 ∉ basis.columns) (weight : Fin width → ℚ) :
    (∑ job : Fin width, weight job * (Arithmetic.value (Direction.assemble width matrix basis free.val)[job.val]! : ℚ)) =
      weight free * (Arithmetic.value basis.determinant : ℚ) +
      ∑ j : Fin basis.columns.size, weight (columnIndex indices j) *
        (Arithmetic.value (Direction.coefficient width matrix basis free.val j.val) : ℚ) := by
  have different (j : Fin basis.columns.size) : columnIndex indices j ≠ free := by
    intro equal
    apply fresh
    have word : free.val.toUInt64 = basis.columns[j.val]! := by
      have same := congrArg Fin.val equal
      change basis.columns[j.val]!.toNat = free.val at same
      rw [← same]
      exact UInt64.ofNat_toNat
    rw [word, getElem!_pos basis.columns j.val j.isLt]
    exact Array.getElem_mem j.isLt
  rw [sum_support (columnIndex indices) (columnIndex_injective indices) free different]
  · rw [Direction.assemble_free _ _ _ _ free.isLt fresh]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show (columnIndex indices j).val = basis.columns[j.val]!.toNat from rfl,
      Direction.assemble_selected _ _ _ _ _ indices j.isLt]
  · intro job notFree outside
    have untouched : (Direction.assemble width matrix basis free.val)[job.val]! =
        ((Array.replicate width (0 : UInt64)).set! free.val basis.determinant)[job.val]! := by
      apply Scatter.untouched
      intro j hj same
      exact outside ⟨j, List.mem_range.mp hj⟩ (Fin.ext same.symm)
    rw [untouched, Array.getElem!_set!_ne _ _ _ _ (by
      intro equal; exact notFree (Fin.ext equal.symm))]
    simp [Arithmetic.value]

end Project.Beck.Sparse
