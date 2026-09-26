import Project.Beck.Direction

namespace Project.Beck.Minor

open LeanExe.Examples.Beck

def rational (k width : Nat) (matrix rows columns : Array UInt64) : Matrix (Fin k) (Fin k) ℚ :=
  (Determinant.minor k width matrix rows columns).map fun w => (Arithmetic.value w : ℚ)

theorem determinant_rational (k width : Nat) (matrix rows columns : Array UInt64)
    (hr : rows.size = k) (hc : columns.size = k) (hk : k ≤ 6)
    (binary : ∀ i j, Determinant.minor k width matrix rows columns i j = 0 ∨
      Determinant.minor k width matrix rows columns i j = 1) :
    (Arithmetic.value (determinant k width matrix rows columns) : ℚ) =
      (rational k width matrix rows columns).det := by
  have bound := Determinant.zero_one_bound
    ((Determinant.minor k width matrix rows columns).map Arithmetic.value)
    (by intro i j; rcases binary i j with h | h <;> simp [h, Arithmetic.value])
  have factorial : (k.factorial : ℤ) ≤ 720 := by
    exact_mod_cast (Nat.factorial_le hk : k.factorial ≤ Nat.factorial 6)
  have fits : Arithmetic.Fits ((Determinant.minor k width matrix rows columns).map Arithmetic.value).det := by
    dsimp [Arithmetic.Fits]
    rw [abs_le] at bound
    omega
  rw [Determinant.determinant_exact k width matrix rows columns hr hc fits, Int.cast_det]
  rfl

theorem replacement (k width : Nat) (matrix rows columns : Array UInt64)
    (hc : columns.size = k) (j : Fin k) (free : UInt64) :
    rational k width matrix rows (columns.set! j.val free) =
      (rational k width matrix rows columns).updateCol j
        (fun i => (Arithmetic.value matrix[rows[i.val]!.toNat * width + free.toNat]! : ℚ)) := by
  ext i l
  simp only [rational, Matrix.map_apply, Determinant.minor, Matrix.updateCol_apply]
  by_cases same : l = j
  · subst l
    rw [Array.getElem!_set!_self _ _ _ (by omega), ite_eq_left rfl]
  · have different : j.val ≠ l.val := by intro h; exact same (Fin.ext h.symm)
    rw [Array.getElem!_set!_ne _ _ _ _ different, ite_eq_right same]

theorem bordered (k width : Nat) (matrix rows columns : Array UInt64)
    (hr : rows.size = k) (hc : columns.size = k) (row col : UInt64) :
    (rational (k + 1) width matrix (rows.push row) (columns.push col)).submatrix
      finSumFinEquiv finSumFinEquiv =
      Cofactors.border (rational k width matrix rows columns)
        (fun i => (Arithmetic.value matrix[rows[i.val]!.toNat * width + col.toNat]! : ℚ))
        (fun j => (Arithmetic.value matrix[row.toNat * width + columns[j.val]!.toNat]! : ℚ))
        (Arithmetic.value matrix[row.toNat * width + col.toNat]!) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [rational, Determinant.minor, Cofactors.border, Matrix.submatrix_apply,
        finSumFinEquiv_apply_left, Array.getElem_push, hr, hc, i.isLt, j.isLt]
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [rational, Determinant.minor, Cofactors.border, Matrix.submatrix_apply,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Array.getElem_push, hr, hc, i.isLt]
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    cases j with
    | inl j =>
      simp [rational, Determinant.minor, Cofactors.border, Matrix.submatrix_apply,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Array.getElem_push, hr, hc, j.isLt]
    | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [rational, Determinant.minor, Cofactors.border, Matrix.submatrix_apply,
        finSumFinEquiv_apply_right, Array.getElem_push, hr, hc]

theorem basis_det (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (positive : 0 < input.jobs) (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (rank : basis.rows.size ≤ 5)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1) :
    (Arithmetic.value basis.determinant : ℚ) =
      (rational basis.rows.size input.jobs (protectedMatrix input x) basis.rows basis.columns).det := by
  rw [wf.value]
  exact determinant_rational _ _ _ _ _ rfl wf.square.symm (by omega)
    (MatrixBasis.minor_binary input x basis positive wf binary)

theorem coefficient_rational (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (positive : 0 < input.jobs) (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (rank : basis.rows.size ≤ 5)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (free : Nat) (freeBound : free < input.jobs) (j : Fin basis.rows.size) :
    (Arithmetic.value (Direction.coefficient input.jobs (protectedMatrix input x) basis free j.val) : ℚ) =
      -(rational basis.rows.size input.jobs (protectedMatrix input x) basis.rows basis.columns).cramer
        (fun i => (Arithmetic.value ((protectedMatrix input x)[
          basis.rows[i.val]!.toNat * input.jobs + free.toUInt64.toNat]!) : ℚ)) j := by
  have bound := MatrixBasis.replacement_determinant_bound input x basis positive wf rank binary free j.val freeBound
  have fits : Arithmetic.Fits (Arithmetic.value 0 - Arithmetic.value
      (determinant basis.rows.size input.jobs (protectedMatrix input x) basis.rows
        (basis.columns.set! j.val free.toUInt64))) := by
    simp only [Arithmetic.Fits, Arithmetic.value] at *
    rw [abs_le] at bound
    norm_num at *
    omega
  rw [Direction.coefficient, Arithmetic.sub_exact _ _ fits]
  rw [show Arithmetic.value (0 : UInt64) = 0 from rfl, zero_sub, Int.cast_neg]
  rw [determinant_rational _ _ _ _ _ rfl (by simpa using wf.square.symm) (by omega)
    (MatrixBasis.replacement_binary input x basis positive wf binary free j.val freeBound),
    replacement _ _ _ _ _ wf.square.symm, Matrix.cramer_apply]

end Project.Beck.Minor
