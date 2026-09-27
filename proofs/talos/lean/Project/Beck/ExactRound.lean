import Project.Beck.ExactUpdate

namespace Project.Beck.ExactRound

open LeanExe.Examples.BeckExact IntegerAdd ExactState
open LeanExe.Examples.Beck (Input)

theorem correct (input : Input) (point : Point)
    (fits : input.jobs ≤ UInt64.size)
    (binary : ∀ job : Fin input.jobs, ∀ category : Fin input.categories,
      input.incidence[job.val * input.categories + category.val]! = 0 ∨
        input.incidence[job.val * input.categories + category.val]! = 1)
    (overlap : ∀ job : Fin input.jobs,
      (Finset.univ.filter fun category => job ∈ ExactCounting.members input category).card ≤ input.overlap)
    (state : ExactState.Valid input.jobs point)
    (nonempty : (ExactCounting.live input point).Nonempty) :
    ∃ next, LeanExe.Examples.BeckExact.round input point = some next ∧
      ExactState.Valid input.jobs next ∧
      (∀ job : Fin input.jobs, frozen point job.val = true → coordinate next job.val = coordinate point job.val) ∧
      (∃ job : Fin input.jobs, frozen point job.val = false ∧ frozen next job.val = true) ∧
      (∀ category : Fin input.categories, input.overlap < liveCount input point category.val →
        ∑ job ∈ ExactCounting.members input category, coordinate next job.val =
          ∑ job ∈ ExactCounting.members input category, coordinate point job.val) := by
  obtain ⟨vector, source, valid, size, moving, fixed, sums⟩ :=
    ExactDirection.correct input point fits binary overlap nonempty
  have entryValid (job : ℕ) (inside : job < input.jobs) : IntegerAdd.Valid vector[job]! :=
    Elimination.get_valid _ valid job (by rw [size]; exact inside)
  obtain ⟨first, firstBound, firstMoving, chosen, stepValid, distancePositive, speedPositive, least⟩ :=
    ExactBoundary.correct state vector size valid
      (fun job inside => fixed ⟨job, inside⟩) (by
        obtain ⟨job, moves⟩ := moving
        exact ⟨job.val, job.isLt, moves⟩)
  let step := boundaryStep point vector
  let next := ExactUpdate.update input.jobs point vector step
  have nextValid : ExactState.Valid input.jobs next := by
    apply ExactUpdate.valid state vector step stepValid entryValid distancePositive.le speedPositive
    intro job inside moves
    have bounds := least job inside moves
    have values := ExactBoundary.candidate_correct state vector job inside (entryValid job inside)
    rwa [values.2.1, values.2.2] at bounds
  have coordinates (job : Fin input.jobs) : coordinate next job.val = coordinate point job.val +
      ((value step.1 : ℚ) / ((value point.denominator * value step.2 : ℤ) : ℚ)) *
        (value vector[job.val]! : ℚ) :=
    ExactUpdate.coordinate state vector step stepValid speedPositive job.val job.isLt (entryValid job.val job.isLt)
  refine ⟨next, ?_, nextValid, ?_, ?_, ?_⟩
  · rw [ExactUpdate.source_eq input point vector source]
    have flag : Integer.isZero step.2 = false := by
      rw [← Bool.not_eq_true, isZero_correct]
      exact ne_of_gt speedPositive
    simp only [show Integer.isZero (boundaryStep point vector).2 = false from flag,
      Bool.false_eq_true, ite_false]
    rfl
  · intro job frozenJob
    rw [coordinates job, fixed job frozenJob]
    simp
  · refine ⟨⟨first, firstBound⟩, Bool.eq_false_iff.mpr (fun flag => firstMoving (fixed ⟨first, firstBound⟩ flag)), ?_⟩
    apply (frozen_iff nextValid first firstBound).mpr
    rw [ExactUpdate.get_eq input.jobs point vector step first firstBound,
      (ExactUpdate.numerator_correct state vector step stepValid first firstBound (entryValid first firstBound)).2]
    change |value point.numerators[first]! * value step.2 + value step.1 * value vector[first]!| =
      value (Integer.mul point.denominator step.2)
    rw [(IntegerMul.mul_correct _ _ state.denominator stepValid.2.1).2]
    change |value point.numerators[first]! * value step.2 + value step.1 * value vector[first]!| =
      value point.denominator * value step.2
    have values := ExactBoundary.candidate_correct state vector first firstBound (entryValid first firstBound)
    change step = _ at chosen
    rw [chosen, values.2.1, values.2.2]
    exact RoundBounds.boundary _ _ _ state.positive firstMoving
  · intro category kept
    simp_rw [coordinates]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have zero : ∑ job ∈ ExactCounting.members input category, (value vector[job.val]! : ℚ) = 0 := by
      exact_mod_cast sums category kept
    rw [zero, mul_zero, add_zero]

#print axioms correct

end Project.Beck.ExactRound
