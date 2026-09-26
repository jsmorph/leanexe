import LeanExe.TypeSafety.Execution

/-!
# Exact execution of core sums and Unit elimination

The laws below quantify over arbitrary operand expressions and all raw values.
They distinguish operand failure from selected-branch failure. A malformed
eliminator input remains stuck, and the laws impose no typing or termination
premise. Branch environments contain the payload before the captured context.
-/

namespace LeanExe.TypeSafety
namespace SumExecution

theorem ret_returns_iff : Steps program (.ret value []) (.ret result []) ↔ result = value := by
  constructor
  · intro execution
    exact (State.ret.inj (execution.eq_of_no_step rfl)).1
  · intro same
    cases same
    exact .refl

theorem ret_not_overflows : ¬ Steps program (.ret value []) (.overflow operation left right) := by
  intro execution
  have impossible := execution.eq_of_no_step rfl
  cases impossible

theorem ret_not_reaches_stuck :
    ¬ ∃ final, Steps program (.ret value []) final ∧ Stuck program final := by
  intro witness
  obtain ⟨final, execution, stuck⟩ := witness
  have same := execution.eq_of_no_step rfl
  cases same
  exact stuck.2 True.intro

theorem returns_iff_of_step_to_return (first : Step program before (.ret value [])) :
    Steps program before (.ret result []) ↔ result = value :=
  (steps_iff_of_step_to_no_step first rfl).trans ret_returns_iff

theorem not_overflows_of_step_to_return (first : Step program before (.ret value [])) :
    ¬ Steps program before (.overflow operation left right) :=
  fun execution => ret_not_overflows ((steps_iff_of_step_to_no_step first rfl).mp execution)

theorem not_reaches_stuck_of_step_to_return (first : Step program before (.ret value [])) :
    ¬ ∃ final, Steps program before final ∧ Stuck program final :=
  fun witness => ret_not_reaches_stuck ((reaches_stuck_iff_of_step first).mp witness)

theorem frame_not_returns_of_no_step
    (noStep : step program (.ret value (frame :: kont)) = none) :
    ¬ Steps program (.ret value (frame :: kont)) (.ret result []) := by
  intro execution
  have impossible := execution.eq_of_no_step noStep
  cases impossible

theorem frame_not_overflows_of_no_step
    (noStep : step program (.ret value (frame :: kont)) = none) :
    ¬ Steps program (.ret value (frame :: kont)) (.overflow operation left right) := by
  intro execution
  have impossible := execution.eq_of_no_step noStep
  cases impossible

theorem frame_reaches_stuck_of_no_step
    (noStep : step program (.ret value (frame :: kont)) = none) :
    ∃ final, Steps program (.ret value (frame :: kont)) final ∧ Stuck program final :=
  ⟨_, .refl, noStep, fun impossible => impossible⟩

theorem unitBody_returns_iff (value : Value) :
    Steps program (.ret value [.unitBody body env]) (.ret result []) ↔
      match value with
      | .unit => Steps program (.eval body env []) (.ret result [])
      | _ => False := by
  cases value
  case unit => exact steps_iff_of_step_to_no_step rfl rfl
  all_goals exact ⟨frame_not_returns_of_no_step rfl, False.elim⟩

theorem unitBody_overflows_iff (value : Value) :
    Steps program (.ret value [.unitBody body env]) (.overflow operation left right) ↔
      match value with
      | .unit => Steps program (.eval body env []) (.overflow operation left right)
      | _ => False := by
  cases value
  case unit => exact steps_iff_of_step_to_no_step rfl rfl
  all_goals exact ⟨frame_not_overflows_of_no_step rfl, False.elim⟩

theorem unitBody_reaches_stuck_iff (value : Value) :
    (∃ final, Steps program (.ret value [.unitBody body env]) final ∧ Stuck program final) ↔
      match value with
      | .unit => ∃ final, Steps program (.eval body env []) final ∧ Stuck program final
      | _ => True := by
  cases value
  case unit => exact reaches_stuck_iff_of_step rfl
  all_goals exact ⟨fun _ => True.intro, fun _ => frame_reaches_stuck_of_no_step rfl⟩

theorem sumBranches_returns_iff (value : Value) :
    Steps program (.ret value [.sumBranches leftBody rightBody env]) (.ret result []) ↔
      match value with
      | .inl payload => Steps program (.eval leftBody (payload :: env) []) (.ret result [])
      | .inr payload => Steps program (.eval rightBody (payload :: env) []) (.ret result [])
      | _ => False := by
  cases value
  case inl => exact steps_iff_of_step_to_no_step rfl rfl
  case inr => exact steps_iff_of_step_to_no_step rfl rfl
  all_goals exact ⟨frame_not_returns_of_no_step rfl, False.elim⟩

theorem sumBranches_overflows_iff (value : Value) :
    Steps program (.ret value [.sumBranches leftBody rightBody env]) (.overflow operation left right) ↔
      match value with
      | .inl payload =>
          Steps program (.eval leftBody (payload :: env) []) (.overflow operation left right)
      | .inr payload =>
          Steps program (.eval rightBody (payload :: env) []) (.overflow operation left right)
      | _ => False := by
  cases value
  case inl => exact steps_iff_of_step_to_no_step rfl rfl
  case inr => exact steps_iff_of_step_to_no_step rfl rfl
  all_goals exact ⟨frame_not_overflows_of_no_step rfl, False.elim⟩

theorem sumBranches_reaches_stuck_iff (value : Value) :
    (∃ final, Steps program (.ret value [.sumBranches leftBody rightBody env]) final ∧
      Stuck program final) ↔
      match value with
      | .inl payload =>
          ∃ final,
            Steps program (.eval leftBody (payload :: env) []) final ∧ Stuck program final
      | .inr payload =>
          ∃ final,
            Steps program (.eval rightBody (payload :: env) []) final ∧ Stuck program final
      | _ => True := by
  cases value
  case inl => exact reaches_stuck_iff_of_step rfl
  case inr => exact reaches_stuck_iff_of_step rfl
  all_goals exact ⟨fun _ => True.intro, fun _ => frame_reaches_stuck_of_no_step rfl⟩

end SumExecution

/-- The payload is evaluated before its returned value is wrapped. -/
theorem inl_returns_iff :
    Steps program (.eval (.inl other payload) env []) (.ret result []) ↔
      ∃ value, Steps program (.eval payload env []) (.ret value []) ∧ result = .inl value := by
  refine (sequence_returns_iff (operand := .eval payload env []) (suffix := [.inl])
    (before := .eval (.inl other payload) env []) rfl).trans ?_
  exact exists_congr (fun value => and_congr Iff.rfl
    (SumExecution.returns_iff_of_step_to_return
      (before := .ret value [.inl]) (value := .inl value) rfl))

theorem inl_overflows_iff :
    Steps program (.eval (.inl other payload) env []) (.overflow operation left right) ↔
      Steps program (.eval payload env []) (.overflow operation left right) := by
  refine (sequence_overflows_iff (operand := .eval payload env []) (suffix := [.inl])
    (before := .eval (.inl other payload) env []) rfl).trans ?_
  constructor
  · intro overflow
    rcases overflow with operandOverflow | continued
    · exact operandOverflow
    · obtain ⟨value, _, impossible⟩ := continued
      exact False.elim (SumExecution.not_overflows_of_step_to_return
        (before := .ret value [.inl]) (value := .inl value) rfl impossible)
  · exact fun overflow => .inl overflow

theorem inl_reaches_stuck_iff :
    (∃ final, Steps program (.eval (.inl other payload) env []) final ∧ Stuck program final) ↔
      ∃ final, Steps program (.eval payload env []) final ∧ Stuck program final := by
  refine (sequence_reaches_stuck_iff (operand := .eval payload env []) (suffix := [.inl])
    (before := .eval (.inl other payload) env []) rfl).trans ?_
  constructor
  · intro stuck
    rcases stuck with operandStuck | continued
    · exact operandStuck
    · obtain ⟨value, final, _, execution, failure⟩ := continued
      exact False.elim (SumExecution.not_reaches_stuck_of_step_to_return
        (before := .ret value [.inl]) (value := .inl value) rfl ⟨final, execution, failure⟩)
  · exact fun stuck => .inl stuck

/-- The payload is evaluated before its returned value is wrapped. -/
theorem inr_returns_iff :
    Steps program (.eval (.inr other payload) env []) (.ret result []) ↔
      ∃ value, Steps program (.eval payload env []) (.ret value []) ∧ result = .inr value := by
  refine (sequence_returns_iff (operand := .eval payload env []) (suffix := [.inr])
    (before := .eval (.inr other payload) env []) rfl).trans ?_
  exact exists_congr (fun value => and_congr Iff.rfl
    (SumExecution.returns_iff_of_step_to_return
      (before := .ret value [.inr]) (value := .inr value) rfl))

theorem inr_overflows_iff :
    Steps program (.eval (.inr other payload) env []) (.overflow operation left right) ↔
      Steps program (.eval payload env []) (.overflow operation left right) := by
  refine (sequence_overflows_iff (operand := .eval payload env []) (suffix := [.inr])
    (before := .eval (.inr other payload) env []) rfl).trans ?_
  constructor
  · intro overflow
    rcases overflow with operandOverflow | continued
    · exact operandOverflow
    · obtain ⟨value, _, impossible⟩ := continued
      exact False.elim (SumExecution.not_overflows_of_step_to_return
        (before := .ret value [.inr]) (value := .inr value) rfl impossible)
  · exact fun overflow => .inl overflow

theorem inr_reaches_stuck_iff :
    (∃ final, Steps program (.eval (.inr other payload) env []) final ∧ Stuck program final) ↔
      ∃ final, Steps program (.eval payload env []) final ∧ Stuck program final := by
  refine (sequence_reaches_stuck_iff (operand := .eval payload env []) (suffix := [.inr])
    (before := .eval (.inr other payload) env []) rfl).trans ?_
  constructor
  · intro stuck
    rcases stuck with operandStuck | continued
    · exact operandStuck
    · obtain ⟨value, final, _, execution, failure⟩ := continued
      exact False.elim (SumExecution.not_reaches_stuck_of_step_to_return
        (before := .ret value [.inr]) (value := .inr value) rfl ⟨final, execution, failure⟩)
  · exact fun stuck => .inl stuck

theorem unitCase_returns_iff :
    Steps program (.eval (.unitCase scrutinee body) env []) (.ret result []) ↔
      ∃ value, Steps program (.eval scrutinee env []) (.ret value []) ∧
        match value with
        | .unit => Steps program (.eval body env []) (.ret result [])
        | _ => False := by
  refine (sequence_returns_iff (operand := .eval scrutinee env [])
    (suffix := [.unitBody body env]) (before := .eval (.unitCase scrutinee body) env []) rfl).trans ?_
  exact exists_congr (fun value => and_congr Iff.rfl (SumExecution.unitBody_returns_iff value))

theorem unitCase_overflows_iff :
    Steps program (.eval (.unitCase scrutinee body) env []) (.overflow operation left right) ↔
      Steps program (.eval scrutinee env []) (.overflow operation left right) ∨
        ∃ value, Steps program (.eval scrutinee env []) (.ret value []) ∧
          match value with
          | .unit => Steps program (.eval body env []) (.overflow operation left right)
          | _ => False := by
  refine (sequence_overflows_iff (operand := .eval scrutinee env [])
    (suffix := [.unitBody body env]) (before := .eval (.unitCase scrutinee body) env []) rfl).trans ?_
  exact or_congr Iff.rfl (exists_congr (fun value =>
    and_congr Iff.rfl (SumExecution.unitBody_overflows_iff value)))

theorem unitCase_reaches_stuck_iff :
    (∃ final, Steps program (.eval (.unitCase scrutinee body) env []) final ∧ Stuck program final) ↔
      (∃ final, Steps program (.eval scrutinee env []) final ∧ Stuck program final) ∨
        ∃ value, Steps program (.eval scrutinee env []) (.ret value []) ∧
          match value with
          | .unit => ∃ final, Steps program (.eval body env []) final ∧ Stuck program final
          | _ => True := by
  refine (sequence_reaches_stuck_iff (operand := .eval scrutinee env [])
    (suffix := [.unitBody body env]) (before := .eval (.unitCase scrutinee body) env []) rfl).trans ?_
  exact or_congr Iff.rfl (exists_congr (fun value =>
    exists_and_left.trans (and_congr Iff.rfl (SumExecution.unitBody_reaches_stuck_iff value))))

theorem sumCase_returns_iff :
    Steps program (.eval (.sumCase scrutinee leftBody rightBody) env []) (.ret result []) ↔
      ∃ value, Steps program (.eval scrutinee env []) (.ret value []) ∧
        match value with
        | .inl payload => Steps program (.eval leftBody (payload :: env) []) (.ret result [])
        | .inr payload => Steps program (.eval rightBody (payload :: env) []) (.ret result [])
        | _ => False := by
  refine (sequence_returns_iff (operand := .eval scrutinee env [])
    (suffix := [.sumBranches leftBody rightBody env])
    (before := .eval (.sumCase scrutinee leftBody rightBody) env []) rfl).trans ?_
  exact exists_congr (fun value => and_congr Iff.rfl (SumExecution.sumBranches_returns_iff value))

theorem sumCase_overflows_iff :
    Steps program (.eval (.sumCase scrutinee leftBody rightBody) env [])
      (.overflow operation left right) ↔
      Steps program (.eval scrutinee env []) (.overflow operation left right) ∨
        ∃ value, Steps program (.eval scrutinee env []) (.ret value []) ∧
          match value with
          | .inl payload =>
              Steps program (.eval leftBody (payload :: env) []) (.overflow operation left right)
          | .inr payload =>
              Steps program (.eval rightBody (payload :: env) []) (.overflow operation left right)
          | _ => False := by
  refine (sequence_overflows_iff (operand := .eval scrutinee env [])
    (suffix := [.sumBranches leftBody rightBody env])
    (before := .eval (.sumCase scrutinee leftBody rightBody) env []) rfl).trans ?_
  exact or_congr Iff.rfl (exists_congr (fun value =>
    and_congr Iff.rfl (SumExecution.sumBranches_overflows_iff value)))

theorem sumCase_reaches_stuck_iff :
    (∃ final, Steps program (.eval (.sumCase scrutinee leftBody rightBody) env []) final ∧
      Stuck program final) ↔
      (∃ final, Steps program (.eval scrutinee env []) final ∧ Stuck program final) ∨
        ∃ value, Steps program (.eval scrutinee env []) (.ret value []) ∧
          match value with
          | .inl payload =>
              ∃ final,
                Steps program (.eval leftBody (payload :: env) []) final ∧ Stuck program final
          | .inr payload =>
              ∃ final,
                Steps program (.eval rightBody (payload :: env) []) final ∧ Stuck program final
          | _ => True := by
  refine (sequence_reaches_stuck_iff (operand := .eval scrutinee env [])
    (suffix := [.sumBranches leftBody rightBody env])
    (before := .eval (.sumCase scrutinee leftBody rightBody) env []) rfl).trans ?_
  exact or_congr Iff.rfl (exists_congr (fun value =>
    exists_and_left.trans (and_congr Iff.rfl (SumExecution.sumBranches_reaches_stuck_iff value))))

end LeanExe.TypeSafety
