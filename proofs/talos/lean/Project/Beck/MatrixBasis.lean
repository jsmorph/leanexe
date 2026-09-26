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

end Project.Beck.MatrixBasis
