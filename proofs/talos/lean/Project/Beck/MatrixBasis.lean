import Project.Beck.FreeColumn

namespace Project.Beck.MatrixBasis

open LeanExe.Examples.Beck
open scoped UInt64.CommRing

theorem index_bound {upper : Nat} {xs : Array UInt64} (h : Basis.Indices upper xs)
    (j : Nat) (hj : j < xs.size) : xs[j]!.toNat < upper := by
  apply h.bound
  rw [getElem!_pos xs j hj]
  exact Array.getElem_mem hj

theorem row_count (input : Input) (x : Point) (positive : 0 < input.jobs) :
    (protectedMatrix input x).size / input.jobs = (ProtectedMatrix.selected input x).length := by
  rw [ProtectedMatrix.protectedMatrix_size, Nat.mul_div_cancel _ positive,
    ProtectedMatrix.selected_length]

theorem indices_binary (input : Input) (x : Point) (k : Nat) (rows columns : Array UInt64)
    (positive : 0 < input.jobs)
    (rowIndices : Basis.Indices ((protectedMatrix input x).size / input.jobs) rows)
    (colIndices : Basis.Indices input.jobs columns) (hr : rows.size = k) (hc : columns.size = k)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (i j : Fin k) :
    Determinant.minor k input.jobs (protectedMatrix input x) rows columns i j = 0 ∨
      Determinant.minor k input.jobs (protectedMatrix input x) rows columns i j = 1 := by
  apply ProtectedMatrix.protectedMatrix_binary input x binary
  · rw [← row_count input x positive]
    exact index_bound rowIndices i.val (hr ▸ i.isLt)
  · exact index_bound colIndices j.val (hc ▸ j.isLt)

theorem selected_column_live (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (positive : 0 < input.jobs) (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (j : Nat) (hj : j < basis.columns.size) : frozen x basis.columns[j]!.toNat = false := by
  by_contra hf
  have frozen : frozen x basis.columns[j]!.toNat = true := by
    cases h : frozen x basis.columns[j]!.toNat <;> simp_all
  have hj' : j < basis.rows.size := by rw [wf.square]; exact hj
  have zero := Matrix.det_eq_zero_of_column_eq_zero
    (A := Determinant.minor basis.rows.size input.jobs (protectedMatrix input x) basis.rows basis.columns)
    (⟨j, hj'⟩ : Fin basis.rows.size) (by
      intro i
      apply ProtectedMatrix.frozen_column_zero
      · rw [← row_count input x positive]
        exact index_bound wf.rows i.val i.isLt
      · exact index_bound wf.columns j hj
      · exact frozen)
  apply wf.nonzero
  rw [wf.value, Determinant.determinant_eq _ _ _ _ _ rfl wf.square.symm]
  exact zero

theorem minor_binary (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (positive : 0 < input.jobs) (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (i j : Fin basis.rows.size) :
    Determinant.minor basis.rows.size input.jobs (protectedMatrix input x) basis.rows basis.columns i j = 0 ∨
      Determinant.minor basis.rows.size input.jobs (protectedMatrix input x) basis.rows basis.columns i j = 1 := by
  apply ProtectedMatrix.protectedMatrix_binary input x binary
  · rw [← row_count input x positive]
    exact index_bound wf.rows i.val i.isLt
  · exact index_bound wf.columns j.val (wf.square ▸ j.isLt)

theorem basis_determinant_bound (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (positive : 0 < input.jobs) (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (rank : basis.rows.size ≤ 5)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1) :
    |Arithmetic.value basis.determinant| ≤ 120 := by
  rw [wf.value]
  exact (Determinant.determinant_small_binary _ _ _ _ _ rfl wf.square.symm rank
    (minor_binary input x basis positive wf binary)).2

theorem replacement_binary (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (positive : 0 < input.jobs) (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (free col : Nat) (freeBound : free < input.jobs)
    (i j : Fin basis.rows.size) :
    let a := Determinant.minor basis.rows.size input.jobs (protectedMatrix input x)
      basis.rows (basis.columns.set! col free.toUInt64) i j
    a = 0 ∨ a = 1 := by
  dsimp only [Determinant.minor]
  apply ProtectedMatrix.protectedMatrix_binary input x binary
  · rw [← row_count input x positive]
    exact index_bound wf.rows i.val i.isLt
  · by_cases same : col = j.val
    · subst col
      rw [Array.getElem!_set!_self _ _ _ (wf.square ▸ j.isLt)]
      change free % 18446744073709551616 < input.jobs
      exact (Nat.mod_le _ _).trans_lt freeBound
    · rw [Array.getElem!_set!_ne _ _ _ _ same]
      exact index_bound wf.columns j.val (wf.square ▸ j.isLt)

theorem replacement_determinant_bound (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (positive : 0 < input.jobs) (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (rank : basis.rows.size ≤ 5)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (free col : Nat) (freeBound : free < input.jobs) :
    |Arithmetic.value (determinant basis.rows.size input.jobs (protectedMatrix input x)
      basis.rows (basis.columns.set! col free.toUInt64))| ≤ 120 := by
  exact (Determinant.determinant_small_binary _ _ _ _ _ rfl
    (by simpa using wf.square.symm) rank
    (replacement_binary input x basis positive wf binary free col freeBound)).2

end Project.Beck.MatrixBasis
