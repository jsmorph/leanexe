import Project.Beck.ExactBoundary
import Project.Beck.RoundBounds

namespace Project.Beck.ExactUpdate

open LeanExe.Examples.BeckExact IntegerAdd BoundarySelect
open LeanExe.Examples.Beck (Input)

def numerator (point : Point) (vector : Array Integer) (step : Step) (job : ℕ) : Integer :=
  Integer.add (Integer.mul point.numerators[job]! step.2) (Integer.mul step.1 vector[job]!)

def update (jobs : ℕ) (point : Point) (vector : Array Integer) (step : Step) : Point :=
  ⟨Integer.mul point.denominator step.2, ((List.range jobs).map (numerator point vector step)).toArray⟩

theorem source_eq (input : Input) (point : Point) (vector : Array Integer)
    (direction : LeanExe.Examples.BeckExact.direction input point = some vector) :
    round input point = if Integer.isZero (boundaryStep point vector).2 then none
      else some (update input.jobs point vector (boundaryStep point vector)) := by
  have loop (step : Step) :
      (forIn (List.range input.jobs) #[] (fun job acc =>
        pure (.yield (acc.push (numerator point vector step job)))) : Option (Array Integer)) =
        some (((List.range input.jobs).map (numerator point vector step)).toArray) := by
    rw [List.forIn_pure_yield_eq_foldl]
    simp only [List.foldl_push_eq_append, Array.empty_append]
    rfl
  rw [LeanExe.Examples.BeckExact.round, direction]
  change ((pure vector : Option (Array Integer)) >>= _) = _
  rw [pure_bind]
  dsimp only
  split_ifs
  · rfl
  · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
    change ((forIn (List.range input.jobs) #[] (fun job acc =>
      pure (.yield (acc.push (numerator point vector (boundaryStep point vector) job))))) >>= _) = _
    rw [loop]
    rfl

theorem get_eq (jobs : ℕ) (point : Point) (vector : Array Integer) (step : Step)
    (job : ℕ) (inside : job < jobs) :
    (update jobs point vector step).numerators[job]! = numerator point vector step job := by
  have bound : job < (update jobs point vector step).numerators.size := by simpa [update] using inside
  rw [getElem!_pos (update jobs point vector step).numerators job bound]
  simp [update]

theorem numerator_correct {jobs : ℕ} {point : Point} (state : ExactState.Valid jobs point)
    (vector : Array Integer) (step : Step) (stepValid : ValidStep step)
    (job : ℕ) (inside : job < jobs) (valid : Valid vector[job]!) :
    Valid (numerator point vector step job) ∧
      value (numerator point vector step job) = value point.numerators[job]! * value step.2 +
        value step.1 * value vector[job]! := by
  have first := IntegerMul.mul_correct _ _ (ExactState.numerator_valid state job inside) stepValid.2.1
  have second := IntegerMul.mul_correct _ _ stepValid.1 valid
  have added := add_correct _ _ first.1 second.1
  exact ⟨added.1, by rw [numerator, added.2, first.2, second.2]⟩

theorem valid {jobs : ℕ} {point : Point} (state : ExactState.Valid jobs point)
    (vector : Array Integer) (step : Step) (stepValid : ValidStep step)
    (vectorValid : ∀ job, job < jobs → Valid vector[job]!)
    (distanceNonnegative : 0 ≤ value step.1) (speedPositive : 0 < value step.2)
    (limit : ∀ job, job < jobs → value vector[job]! ≠ 0 →
      value step.1 * |value vector[job]!| ≤
        (if value vector[job]! < 0 then value point.denominator + value point.numerators[job]!
         else value point.denominator - value point.numerators[job]!) * value step.2) :
    ExactState.Valid jobs (update jobs point vector step) := by
  have denominator := IntegerMul.mul_correct _ _ state.denominator stepValid.2.1
  refine ⟨by simp [update], ?_, denominator.1, ?_, ?_⟩
  · intro entry member
    obtain ⟨job, inside, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp member)
    exact (numerator_correct state vector step stepValid job (List.mem_range.mp inside)
      (vectorValid job (List.mem_range.mp inside))).1
  · change 0 < value (Integer.mul point.denominator step.2)
    rw [denominator.2]
    exact mul_pos state.positive speedPositive
  · intro job inside
    rw [get_eq jobs point vector step job inside,
      (numerator_correct state vector step stepValid job inside (vectorValid job inside)).2]
    change |value point.numerators[job]! * value step.2 + value step.1 * value vector[job]!| ≤
      value (Integer.mul point.denominator step.2)
    rw [denominator.2]
    exact RoundBounds.inside _ _ _ _ _ (state.cube job inside) distanceNonnegative speedPositive (limit job inside)

theorem coordinate {jobs : ℕ} {point : Point} (state : ExactState.Valid jobs point)
    (vector : Array Integer) (step : Step) (stepValid : ValidStep step)
    (speedPositive : 0 < value step.2) (job : ℕ) (inside : job < jobs) (valid : Valid vector[job]!) :
    ExactState.coordinate (update jobs point vector step) job = ExactState.coordinate point job +
      ((value step.1 : ℚ) / ((value point.denominator * value step.2 : ℤ) : ℚ)) * (value vector[job]! : ℚ) := by
  rw [ExactState.coordinate, get_eq jobs point vector step job inside,
    (numerator_correct state vector step stepValid job inside valid).2]
  change ((value point.numerators[job]! * value step.2 + value step.1 * value vector[job]! : ℤ) : ℚ) /
    (value (Integer.mul point.denominator step.2) : ℚ) = _
  rw [(IntegerMul.mul_correct _ _ state.denominator stepValid.2.1).2]
  exact RoundBounds.coordinate _ _ _ _ _ (ne_of_gt state.positive) (ne_of_gt speedPositive)

#print axioms source_eq
#print axioms valid

end Project.Beck.ExactUpdate
