import LeanExe.TypeSafety.Continuations

/-!
# Finite execution inversion

A known first transition can be removed or restored when the final state has
no successor. This includes ordinary returns, exact overflow records (valid or
malformed), and stuck states. It does not identify every no-successor state with
a permitted terminal outcome.
-/

namespace LeanExe.TypeSafety

/-- A finite execution is empty or has a first transition and a remaining execution. -/
theorem Steps.head_iff : Steps program before after ↔
    before = after ∨ ∃ next, Step program before next ∧ Steps program next after := by
  constructor
  · intro execution
    induction execution with
    | refl => exact .inl rfl
    | tail history transition ih =>
        rcases ih with same | advances
        · cases same
          exact .inr ⟨_, transition, .refl⟩
        · obtain ⟨next, first, remaining⟩ := advances
          exact .inr ⟨next, first, .tail remaining transition⟩
  · intro witness
    rcases witness with same | advances
    · cases same
      exact .refl
    · obtain ⟨next, first, remaining⟩ := advances
      exact (Steps.tail .refl first).trans remaining

/-- A state with no successor cannot have a nonempty finite execution. -/
theorem Steps.eq_of_no_step (execution : Steps program before after)
    (noStep : step program before = none) : after = before := by
  rcases Steps.head_iff.mp execution with same | advances
  · exact same.symm
  · obtain ⟨next, transition, _⟩ := advances
    have impossible : (none : Option State) = some next := noStep.symm.trans transition
    cases impossible

theorem steps_from_no_step_iff (noStep : step program before = none) :
    Steps program before after ↔ after = before := by
  constructor
  · intro execution
    exact execution.eq_of_no_step noStep
  · intro same
    cases same
    exact .refl

/-- Determinism identifies the known first step; the endpoint cannot also be the start. -/
theorem steps_iff_of_step_to_no_step (first : Step program before next)
    (finalNoStep : step program final = none) :
    Steps program before final ↔ Steps program next final := by
  constructor
  · intro execution
    rcases Steps.head_iff.mp execution with same | advances
    · cases same
      have impossible : (none : Option State) = some next := finalNoStep.symm.trans first
      cases impossible
    · obtain ⟨actualNext, actualFirst, remaining⟩ := advances
      have same := step_deterministic first actualFirst
      cases same
      exact remaining
  · intro remaining
    exact (Steps.tail .refl first).trans remaining

/-- A real first transition rules out stuckness at the start, preserving exact reachability. -/
theorem reaches_stuck_iff_of_step (first : Step program before next) :
    (∃ final, Steps program before final ∧ Stuck program final) ↔
      ∃ final, Steps program next final ∧ Stuck program final := by
  constructor
  · intro witness
    obtain ⟨final, execution, stuck⟩ := witness
    exact ⟨final, (steps_iff_of_step_to_no_step first stuck.1).mp execution, stuck⟩
  · intro witness
    obtain ⟨final, execution, stuck⟩ := witness
    exact ⟨final, (steps_iff_of_step_to_no_step first stuck.1).mpr execution, stuck⟩

/-- Decompose an expression's first operand and its pending continuation at an exact return. -/
theorem sequence_returns_iff
    (first : Step program before (operand.appendKont suffix)) :
    Steps program before (.ret result []) ↔
      ∃ value, Steps program operand (.ret value []) ∧
        Steps program (.ret value suffix) (.ret result []) :=
  (steps_iff_of_step_to_no_step first rfl).trans appendKont_returns_iff

/-- A first operand may overflow before its continuation is entered. -/
theorem sequence_overflows_iff
    (first : Step program before (operand.appendKont suffix)) :
    Steps program before (.overflow operation left right) ↔
      Steps program operand (.overflow operation left right) ∨
        ∃ value, Steps program operand (.ret value []) ∧
          Steps program (.ret value suffix) (.overflow operation left right) :=
  (steps_iff_of_step_to_no_step first rfl).trans appendKont_overflows_iff

/-- Distinguish operand stuckness from stuckness after its return to the continuation. -/
theorem sequence_reaches_stuck_iff
    (first : Step program before (operand.appendKont suffix)) :
    (∃ final, Steps program before final ∧ Stuck program final) ↔
      (∃ final, Steps program operand final ∧ Stuck program final) ∨
        ∃ value final, Steps program operand (.ret value []) ∧
          Steps program (.ret value suffix) final ∧ Stuck program final :=
  (reaches_stuck_iff_of_step first).trans appendKont_reaches_stuck_iff

end LeanExe.TypeSafety
