import LeanExe.Source.ScalarStepMatcher
import LeanExe.Source.ExprEquality

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Collect names and binder visibility; full type/body equality is checked later. -/
def stepMatcherShape? : Lean.Expr → Lean.Expr → Option StepMatcher.Shape
  | .forallE motiveName (.forallE motiveArgument _ _ motiveArgumentBi)
      (.forallE scrutineeName _
        (.forallE doneName (.forallE donePayload _ _ donePayloadBi)
          (.forallE yieldName (.forallE yieldPayload _ _ yieldPayloadBi) _ yieldBi) doneBi) scrutineeBi) motiveBi,
    .lam _ _ (.lam _ _ (.lam _ _ (.lam _ _
      (.app (.app (.app (.app (.app _ _) (.lam forwardMotive _ _ forwardMotiveBi)) _)
        (.lam forwardDone _ _ forwardDoneBi)) (.lam forwardYield _ _ forwardYieldBi)) _) _) _) _ =>
      some {
        motive := ⟨motiveName, motiveBi⟩
        motiveArgument := ⟨motiveArgument, motiveArgumentBi⟩
        scrutinee := ⟨scrutineeName, scrutineeBi⟩
        doneHandler := ⟨doneName, doneBi⟩
        donePayload := ⟨donePayload, donePayloadBi⟩
        yieldHandler := ⟨yieldName, yieldBi⟩
        yieldPayload := ⟨yieldPayload, yieldPayloadBi⟩
        forwardMotive := ⟨forwardMotive, forwardMotiveBi⟩
        forwardDone := ⟨forwardDone, forwardDoneBi⟩
        forwardYield := ⟨forwardYield, forwardYieldBi⟩ }
  | _, _ => none

@[simp] theorem stepMatcherShape_accepts (shape : StepMatcher.Shape) (level : Lean.Level) :
    stepMatcherShape? (shape.type level) (shape.value level) = some shape := by
  cases shape
  rfl

/-- Only the exact safe, total, universe-polymorphic forwarding definition is accepted. -/
def findStepMatcher? (env : Lean.Environment) (name : Lean.Name) : Option (Lean.Name × StepMatcher.Shape) := do
  let info ← env.find? name
  if info.isUnsafe || info.isPartial then none else
    match info.levelParams with
    | [level] => do
        let value ← info.value?
        let shape ← stepMatcherShape? info.type value
        if info.type = shape.type (.param level) ∧ value = shape.value (.param level) then
          some (level, shape)
        else none
    | _ => none

theorem findStepMatcher_sound {env : Lean.Environment} {name level : Lean.Name} {shape : StepMatcher.Shape}
    (found : findStepMatcher? env name = some (level, shape)) : StepMatcher.Defined env name := by
  simp only [findStepMatcher?, bind, Option.bind_eq_some_iff] at found
  obtain ⟨info, lookup, found⟩ := found
  split at found
  · contradiction
  · rename_i safeTotal
    have flags : info.isUnsafe = false ∧ info.isPartial = false := by
      simpa using safeTotal
    split at found
    · rename_i parameter parameters
      simp only [Option.bind_eq_some_iff] at found
      obtain ⟨value, body, candidate, _, found⟩ := found
      split at found
      · rename_i same
        exact .intro info parameter candidate lookup parameters flags.1 flags.2 same.1 (body.trans (congrArg some same.2))
      · contradiction
    · contradiction

theorem findStepMatcher_accepts {env : Lean.Environment} {name : Lean.Name}
    (defined : StepMatcher.Defined env name) : ∃ level shape, findStepMatcher? env name = some (level, shape) := by
  cases defined with
  | intro info level shape lookup parameters safe total type value =>
    exact ⟨level, shape, by simp [findStepMatcher?, lookup, parameters, safe, total, type, value]⟩

end LeanExe.Extract.Core
