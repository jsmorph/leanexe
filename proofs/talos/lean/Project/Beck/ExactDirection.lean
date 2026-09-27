import Project.Beck.DirectionSolve
import Project.Beck.ExactMatrix
import Project.Beck.ExactFreeColumn

namespace Project.Beck.ExactDirection

open LeanExe.Examples.BeckExact IntegerAdd
open LeanExe.Examples.Beck (Input)

theorem matrix_correct (input : Input) (point : Point)
    (fits : input.jobs ≤ UInt64.size)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ ExactCounting.members input category).card ≤ input.overlap)
    (nonempty : (ExactCounting.live input point).Nonempty) :
    ∃ result, direction input point = some result ∧
      (∀ entry ∈ result, Valid entry) ∧ result.size = input.jobs ∧
      (∃ job : Fin input.jobs, value result[job.val]! ≠ 0) ∧
      (∀ job : Fin input.jobs, frozen point job.val = true → value result[job.val]! = 0) ∧
      (∀ row : Fin (ExactCounting.protectedRows input point).card,
        ∑ job : Fin input.jobs, value (protectedMatrix input point)[row.val * input.jobs + job.val]! *
          value result[job.val]! = 0) := by
  have positive : 0 < input.jobs := by
    obtain ⟨job, _⟩ := nonempty
    exact (Nat.zero_le job.val).trans_lt job.isLt
  obtain ⟨basis, source, invariant⟩ := EchelonProof.echelon_correct input.jobs
    (ExactCounting.protectedRows input point).card (protectedMatrix input point)
    positive (ExactMatrix.size_eq input point) (ExactMatrix.valid input point)
  have fewer := ExactCounting.protected_fewer input point overlap nonempty
  have freeSpec := ExactFreeColumn.search_correct input point basis.columns
    (ExactFreeColumn.exists_free input point basis.columns fits (invariant.1.rankBound.trans_lt fewer))
  let free : Fin input.jobs := ⟨freeColumn input point basis.columns, freeSpec.1⟩
  obtain ⟨result, backward, valid, size, atFree, other, kernel⟩ := DirectionSolve.backward_correct
    input.jobs (ExactCounting.protectedRows input point).card (protectedMatrix input point) basis
    invariant fits free freeSpec.2.2
  refine ⟨result, ?_, valid, size, ⟨free, ?_⟩, ?_, kernel⟩
  · rw [DirectionSolve.source_eq input point basis source, ite_eq_right]
    · exact backward
    · simpa only [beq_iff_eq] using Nat.ne_of_lt freeSpec.1
  · rw [atFree]
    exact invariant.1.nonzero
  · intro job fixed
    have notPivot := EchelonProof.zero_column_not_pivot input.jobs
      (ExactCounting.protectedRows input point).card (protectedMatrix input point) basis invariant fits job
      (by intro row; exact ExactMatrix.frozen_zero input point row.val job.val row.isLt job.isLt fixed)
    apply other job _ notPivot
    intro same
    have atChosen : frozen point free.val = true := same ▸ fixed
    have live : frozen point free.val = false := freeSpec.2.1
    rw [live] at atChosen
    contradiction

theorem category_sum (input : Input) (point : Point) (vector : Array Integer)
    (binary : ∀ job : Fin input.jobs, ∀ category : Fin input.categories,
      input.incidence[job.val * input.categories + category.val]! = 0 ∨
        input.incidence[job.val * input.categories + category.val]! = 1)
    (fixed : ∀ job : Fin input.jobs, frozen point job.val = true → value vector[job.val]! = 0)
    (kernel : ∀ row : Fin (ExactCounting.protectedRows input point).card,
      ∑ job : Fin input.jobs, value (protectedMatrix input point)[row.val * input.jobs + job.val]! *
        value vector[job.val]! = 0)
    (category : Fin input.categories) (kept : input.overlap < liveCount input point category.val) :
    ∑ job ∈ ExactCounting.members input category, value vector[job.val]! = 0 := by
  have member : category.val ∈ ExactMatrix.selected input point := by
    simp [ExactMatrix.selected, category.isLt, kept]
  obtain ⟨row, rowBound, selected⟩ := List.mem_iff_getElem.mp member
  have equation := kernel ⟨row, by rwa [ExactMatrix.selected_length] at rowBound⟩
  have entry (job : Fin input.jobs) :
      value (protectedMatrix input point)[row * input.jobs + job.val]! * value vector[job.val]! =
        if job ∈ ExactCounting.members input category then value vector[job.val]! else 0 := by
    rw [ExactMatrix.get_eq input point row job.val rowBound job.isLt, selected]
    by_cases frozenJob : frozen point job.val = true
    · simp [ExactMatrix.entry, frozenJob, fixed job frozenJob, zero_correct.2]
    · have live : frozen point job.val = false := Bool.eq_false_iff.mpr frozenJob
      simp only [ExactMatrix.entry, live, Bool.false_eq_true, ite_false]
      rw [(IntegerOrder.ofWord_correct _).2]
      rcases binary job category with entry | entry <;> simp [ExactCounting.members, entry]
  simp_rw [entry] at equation
  simpa [ExactCounting.members, Finset.sum_filter] using equation

theorem correct (input : Input) (point : Point)
    (fits : input.jobs ≤ UInt64.size)
    (binary : ∀ job : Fin input.jobs, ∀ category : Fin input.categories,
      input.incidence[job.val * input.categories + category.val]! = 0 ∨
        input.incidence[job.val * input.categories + category.val]! = 1)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ ExactCounting.members input category).card ≤ input.overlap)
    (nonempty : (ExactCounting.live input point).Nonempty) :
    ∃ result, direction input point = some result ∧
      (∀ entry ∈ result, Valid entry) ∧ result.size = input.jobs ∧
      (∃ job : Fin input.jobs, value result[job.val]! ≠ 0) ∧
      (∀ job : Fin input.jobs, frozen point job.val = true → value result[job.val]! = 0) ∧
      (∀ category : Fin input.categories, input.overlap < liveCount input point category.val →
        ∑ job ∈ ExactCounting.members input category, value result[job.val]! = 0) := by
  obtain ⟨result, source, valid, size, moving, fixed, kernel⟩ := matrix_correct input point fits overlap nonempty
  exact ⟨result, source, valid, size, moving, fixed, category_sum input point result binary fixed kernel⟩

#print axioms correct

end Project.Beck.ExactDirection
