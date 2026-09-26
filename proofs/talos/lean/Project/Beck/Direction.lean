import Project.Beck.Scatter
import Project.Beck.Cofactors

namespace Project.Beck.Direction

open LeanExe.Examples.Beck

abbrev sourceBasis (input : Input) (x : Point) :=
  findBasis input.jobs input.jobs (protectedMatrix input x) ⟨#[], #[], 1⟩

def coefficient (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis)
    (free j : Nat) : UInt64 :=
  0 - determinant basis.rows.size width matrix basis.rows (basis.columns.set! j free.toUInt64)

def assemble (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis)
    (free : Nat) : Array UInt64 :=
  Scatter.write (List.range basis.columns.size) (fun j => basis.columns[j]!.toNat)
    (coefficient width matrix basis free)
    ((Array.replicate width (0 : UInt64)).set! free basis.determinant)

theorem direction_eq (input : Input) (x : Point)
    (available : freeColumn input x (sourceBasis input x).columns < input.jobs) :
    direction input x = assemble input.jobs (protectedMatrix input x) (sourceBasis input x)
      (freeColumn input x (sourceBasis input x).columns) := by
  have different : freeColumn input x (sourceBasis input x).columns ≠ input.jobs := Nat.ne_of_lt available
  simp only [direction, sourceBasis, beq_iff_eq, different, ↓reduceIte,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp only [Id.run, bind, pure]
  exact List.forIn_pure_yield_eq_foldl (m := Id) _ _

theorem assemble_size (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis)
    (free : Nat) : (assemble width matrix basis free).size = width := by
  simp [assemble, Scatter.size]

theorem index_list (columns : Array UInt64) :
    (List.range columns.size).map (fun j => columns[j]!.toNat) = columns.toList.map UInt64.toNat := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < columns.size := by simpa using h₁
    simp [getElem!_pos columns i hi]

theorem index_distinct {width : Nat} {columns : Array UInt64} (indices : Basis.Indices width columns) :
    ((List.range columns.size).map fun j => columns[j]!.toNat).Nodup := by
  rw [index_list]
  exact indices.nodup.map (fun _ _ e => UInt64.toNat_inj.mp e)

theorem assemble_selected (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis)
    (free j : Nat) (indices : Basis.Indices width basis.columns) (hj : j < basis.columns.size) :
    (assemble width matrix basis free)[basis.columns[j]!.toNat]! =
      coefficient width matrix basis free j := by
  apply Scatter.written
  · exact index_distinct indices
  · intro k hk
    simpa using MatrixBasis.index_bound indices k (List.mem_range.mp hk)
  · exact List.mem_range.mpr hj

theorem assemble_other (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis)
    (free job : Nat) (fresh : job.toUInt64 ∉ basis.columns) :
    (assemble width matrix basis free)[job]! =
      ((Array.replicate width (0 : UInt64)).set! free basis.determinant)[job]! := by
  apply Scatter.untouched
  intro j hj equality
  have hj' := List.mem_range.mp hj
  apply fresh
  have word : job.toUInt64 = basis.columns[j]! := by
    rw [equality]
    exact UInt64.ofNat_toNat
  rw [word, getElem!_pos basis.columns j hj']
  exact Array.getElem_mem hj'

theorem assemble_free (width : Nat) (matrix : Array UInt64) (basis : LeanExe.Examples.Beck.Basis)
    (free : Nat) (bound : free < width) (fresh : free.toUInt64 ∉ basis.columns) :
    (assemble width matrix basis free)[free]! = basis.determinant := by
  rw [assemble_other width matrix basis free free fresh]
  exact Array.getElem!_set!_self _ _ _ (by simpa)

theorem direction_size_nonzero (input : Input) (x : Point)
    (capacity : input.jobs ≤ 6)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ Counting.members input category).card ≤ input.overlap)
    (nonempty : (Counting.live input x).Nonempty) :
    (direction input x).size = input.jobs ∧ ∃ job < input.jobs, (direction input x)[job]! ≠ 0 := by
  have free := FreeColumn.source_freeColumn input x capacity overlap nonempty
  have wf := (ProtectedMatrix.source_basis_complete input x overlap nonempty).1
  rw [direction_eq input x free.1]
  refine ⟨assemble_size _ _ _ _, freeColumn input x (sourceBasis input x).columns, free.1, ?_⟩
  rw [assemble_free _ _ _ _ free.1 free.2.2]
  exact wf.nonzero

theorem direction_frozen_zero (input : Input) (x : Point)
    (capacity : input.jobs ≤ 6)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ Counting.members input category).card ≤ input.overlap)
    (nonempty : (Counting.live input x).Nonempty)
    (job : Nat) (hj : job < input.jobs) (hf : frozen x job = true) :
    (direction input x)[job]! = 0 := by
  have free := FreeColumn.source_freeColumn input x capacity overlap nonempty
  have wf := (ProtectedMatrix.source_basis_complete input x overlap nonempty).1
  have positive : 0 < input.jobs := (Nat.zero_le job).trans_lt hj
  have fresh : job.toUInt64 ∉ (sourceBasis input x).columns := by
    intro member
    obtain ⟨j, hj', he⟩ := Array.mem_iff_getElem.mp member
    have live := MatrixBasis.selected_column_live input x _ positive wf j hj'
    rw [getElem!_pos (sourceBasis input x).columns j hj', he] at live
    have exactWord : job.toUInt64.toNat = job := by
      change job % 18446744073709551616 = job
      apply Nat.mod_eq_of_lt
      omega
    simp [exactWord, hf] at live
  have different : freeColumn input x (sourceBasis input x).columns ≠ job := by
    intro same
    have := free.2.1
    simp [same, hf] at this
  rw [direction_eq input x free.1, assemble_other _ _ _ _ _ fresh,
    Array.getElem!_set!_ne _ _ _ _ different]
  simp [getElem!_pos (Array.replicate input.jobs (0 : UInt64)) job (by simpa)]

theorem coefficient_bound (input : Input) (x : Point) (basis : LeanExe.Examples.Beck.Basis)
    (positive : 0 < input.jobs) (wf : Basis.WellFormed input.jobs (protectedMatrix input x) basis)
    (rank : basis.rows.size ≤ 5)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (free col : Nat) (freeBound : free < input.jobs) :
    |Arithmetic.value (coefficient input.jobs (protectedMatrix input x) basis free col)| ≤ 120 := by
  have bound := MatrixBasis.replacement_determinant_bound input x basis positive wf rank binary free col freeBound
  unfold coefficient
  rw [Arithmetic.sub_exact]
  · simpa [Arithmetic.value] using bound
  · simp only [Arithmetic.Fits, Arithmetic.value] at *
    rw [abs_le] at bound
    norm_num at *
    omega

theorem direction_bound (input : Input) (x : Point)
    (capacity : input.jobs ≤ 6)
    (binary : ∀ job < input.jobs, ∀ category < input.categories,
      input.incidence[job * input.categories + category]! = 0 ∨
        input.incidence[job * input.categories + category]! = 1)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ Counting.members input category).card ≤ input.overlap)
    (nonempty : (Counting.live input x).Nonempty)
    (job : Nat) (hj : job < input.jobs) : |Arithmetic.value (direction input x)[job]!| ≤ 120 := by
  have free := FreeColumn.source_freeColumn input x capacity overlap nonempty
  have basis := ProtectedMatrix.source_basis_complete input x overlap nonempty
  have positive : 0 < input.jobs := (Nat.zero_le job).trans_lt hj
  have rank : (sourceBasis input x).rows.size ≤ 5 := by
    have bound : (sourceBasis input x).rows.size < input.jobs := basis.2.2
    omega
  rw [direction_eq input x free.1]
  by_cases selected : job.toUInt64 ∈ (sourceBasis input x).columns
  · obtain ⟨j, hj', he⟩ := Array.mem_iff_getElem.mp selected
    have index : (sourceBasis input x).columns[j]!.toNat = job := by
      rw [getElem!_pos (sourceBasis input x).columns j hj', he]
      change job % 18446744073709551616 = job
      apply Nat.mod_eq_of_lt
      omega
    conv_lhs => arg 1; arg 1; rw [← index]
    rw [assemble_selected _ _ _ _ _ basis.1.columns hj']
    exact coefficient_bound input x _ positive basis.1 rank binary _ _ free.1
  · rw [assemble_other _ _ _ _ _ selected]
    by_cases same : freeColumn input x (sourceBasis input x).columns = job
    · rw [same, Array.getElem!_set!_self _ _ _ (by simpa)]
      exact MatrixBasis.basis_determinant_bound input x _ positive basis.1 rank binary
    · rw [Array.getElem!_set!_ne _ _ _ _ same]
      simp [getElem!_pos (Array.replicate input.jobs (0 : UInt64)) job (by simpa), Arithmetic.value]

end Project.Beck.Direction
