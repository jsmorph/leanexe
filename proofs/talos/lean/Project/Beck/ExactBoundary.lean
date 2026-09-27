import Project.Beck.ExactState
import Project.Beck.BoundarySelect

namespace Project.Beck.ExactBoundary

open LeanExe.Examples.BeckExact IntegerAdd BoundarySelect

def gap (point : Point) (vector : Array Integer) (job : ℕ) : Integer :=
  if vector[job]!.negative then Integer.add point.denominator point.numerators[job]!
  else Integer.sub point.denominator point.numerators[job]!

def candidate (point : Point) (vector : Array Integer) (job : ℕ) : Step :=
  (gap point vector job, Integer.abs vector[job]!)

theorem source_eq (point : Point) (vector : Array Integer) :
    boundaryStep point vector = (List.range vector.size).foldl
      (fun old job => select (candidate point vector job) old) (Integer.zero, Integer.zero) := by
  simp only [boundaryStep, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp only [Id.run, bind, pure, Prod.mk.eta, ← apply_ite ForInStep.yield]
  change (forIn (List.range vector.size) (Integer.zero, Integer.zero)
    (fun job old => ForInStep.yield (select (candidate point vector job) old)) : Id Step) = _
  exact List.forIn_pure_yield_eq_foldl (m := Id) _ _

theorem candidate_correct {jobs : ℕ} {point : Point} (state : ExactState.Valid jobs point)
    (vector : Array Integer) (job : ℕ) (inside : job < jobs) (valid : Valid vector[job]!) :
    ValidStep (candidate point vector job) ∧
      value (candidate point vector job).1 =
        (if value vector[job]! < 0 then value point.denominator + value point.numerators[job]!
         else value point.denominator - value point.numerators[job]!) ∧
      value (candidate point vector job).2 = |value vector[job]!| := by
  have absolute := IntegerOrder.abs_correct _ valid
  have sum := add_correct _ _ state.denominator (ExactState.numerator_valid state job inside)
  have difference := sub_correct _ _ state.denominator (ExactState.numerator_valid state job inside)
  simp only [candidate, gap, ExactState.negative_iff _ valid]
  split_ifs
  · exact ⟨⟨sum.1, absolute.1, by rw [absolute.2]; exact abs_nonneg _⟩, sum.2, absolute.2⟩
  · exact ⟨⟨difference.1, absolute.1, by rw [absolute.2]; exact abs_nonneg _⟩, difference.2, absolute.2⟩

theorem moving_iff {jobs : ℕ} {point : Point} (state : ExactState.Valid jobs point)
    (vector : Array Integer) (job : ℕ) (inside : job < jobs) (valid : Valid vector[job]!) :
    Integer.isZero (candidate point vector job).2 = false ↔ value vector[job]! ≠ 0 := by
  rw [← Bool.not_eq_true, isZero_correct, (candidate_correct state vector job inside valid).2.2,
    abs_eq_zero]

theorem gap_positive {jobs : ℕ} {point : Point} (state : ExactState.Valid jobs point)
    (vector : Array Integer) (job : ℕ) (inside : job < jobs) (valid : Valid vector[job]!)
    (fixed : frozen point job = true → value vector[job]! = 0) (moving : value vector[job]! ≠ 0) :
    0 < value (candidate point vector job).1 := by
  have live : frozen point job = false := Bool.eq_false_iff.mpr (fun flag => moving (fixed flag))
  have interior := abs_lt.mp ((ExactState.live_iff state job inside).mp live)
  rw [(candidate_correct state vector job inside valid).2.1]
  split_ifs <;> omega

theorem correct {jobs : ℕ} {point : Point} (state : ExactState.Valid jobs point)
    (vector : Array Integer) (size : vector.size = jobs) (valid : ∀ entry ∈ vector, Valid entry)
    (fixed : ∀ job, job < jobs → frozen point job = true → value vector[job]! = 0)
    (moving : ∃ job < jobs, value vector[job]! ≠ 0) :
    ∃ first < jobs, value vector[first]! ≠ 0 ∧
      boundaryStep point vector = candidate point vector first ∧
      ValidStep (boundaryStep point vector) ∧
      0 < value (boundaryStep point vector).1 ∧ 0 < value (boundaryStep point vector).2 ∧
      ∀ job < jobs, value vector[job]! ≠ 0 →
        value (boundaryStep point vector).1 * value (candidate point vector job).2 ≤
          value (candidate point vector job).1 * value (boundaryStep point vector).2 := by
  have entryValid (job : ℕ) (inside : job < jobs) : Valid vector[job]! :=
    Elimination.get_valid _ valid job (by rw [size]; exact inside)
  have candidates (job : ℕ) (member : job ∈ List.range jobs) : ValidStep (candidate point vector job) :=
    (candidate_correct state vector job (List.mem_range.mp member) (entryValid job (List.mem_range.mp member))).1
  obtain ⟨first, member, flag, source, least⟩ := minimum (candidate point vector) (List.range jobs) candidates (by
    obtain ⟨job, inside, nonzero⟩ := moving
    exact ⟨job, List.mem_range.mpr inside, (moving_iff state vector job inside (entryValid job inside)).mpr nonzero⟩)
  have firstBound := List.mem_range.mp member
  have nonzero := (moving_iff state vector first firstBound (entryValid first firstBound)).mp flag
  have chosen : boundaryStep point vector = candidate point vector first := by rw [source_eq, size, source]
  refine ⟨first, firstBound, nonzero, chosen, ?_, ?_, ?_, ?_⟩
  · rw [chosen]
    exact candidates first member
  · rw [chosen]
    exact gap_positive state vector first firstBound (entryValid first firstBound) (fixed first firstBound) nonzero
  · rw [chosen]
    exact BoundarySelect.positive _ (candidates first member) flag
  · intro job inside nonzero
    rw [chosen]
    exact least job (List.mem_range.mpr inside)
      ((moving_iff state vector job inside (entryValid job inside)).mpr nonzero)

#print axioms correct

end Project.Beck.ExactBoundary
