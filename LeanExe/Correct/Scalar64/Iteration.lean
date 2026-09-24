module
public import Std
import all Init.While
public section

/-!
Terminating iteration, independent of compiler instructions. The bridge to Lean's
actual `repeatM` uses its fixed-point pinning theorem, not its native implementation.
Unlike the independent core, this bridge inherits Classical.choice and Quot.sound
from Lean's definition of repeatM. It introduces no axioms.
-/
namespace LeanExe.Correct.Scalar64

@[expose] def forInStep : ForInStep α → Sum α α
  | .done value => .inr value
  | .yield value => .inl value

/-- Export the unfolding across the new module system's private matcher boundary. -/
theorem loop_forIn_eq (body : Unit → α → ForInStep α) (state : α) :
    Lean.Loop.forIn (m := Id) {} state body =
      @repeatM _ Id _ _ ⟨state⟩ (fun current => forInStep (body () current)) state := rfl

inductive Iterates (step : α → Sum α β) : α → β → Prop where
  | done (eq : step state = .inr result) : Iterates step state result
  | next (eq : step state = .inl following) (rest : Iterates step following result) :
      Iterates step state result

theorem Iterates.repeatM_eq [Nonempty β] {step : α → Sum α β}
    (fixed : ∃ finish : α → β, repeatM.body (m := Id) step finish = finish)
    (execution : Iterates step state result) :
    repeatM (m := Id) step state = result := by
  induction execution with
  | done eq =>
      rw [_root_.repeatM_eq _ fixed]
      simp [repeatM.body, eq, Bind.bind, Pure.pure]
  | next eq rest ih =>
      rw [_root_.repeatM_eq _ fixed]
      simpa [repeatM.body, eq, Bind.bind, Pure.pure] using ih

end LeanExe.Correct.Scalar64
